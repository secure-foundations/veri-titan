import sys, os, subprocess,re
from subprocess import PIPE, Popen

rules = """
rule dafny
    command = dafny /compile:0 $in /timeLimit:20 /vcsCores:8 && touch $out

rule vale
    command = vale -dafnyText -in $in -out $out

rule dfydep
    command = python3 build.py dfydep $in > $out
"""

oupt_file_name = "build.ninja"
ninja_content = [rules]

def get_dot_ver_path(dfy_path):
    dfy_path = os.path.relpath(dfy_path)
    ver_path = dfy_path.replace(".dfy", ".ver")
    if ver_path.startswith("gen"):
        return ver_path
    else:
        return os.path.join("gen", ver_path)

def get_dot_dd_path(dfy_path):
    dfy_path = os.path.relpath(dfy_path)
    dd_path = dfy_path.replace(".dfy", ".dd")
    if dd_path.startswith("gen"):
        return dd_path
    else:
        return os.path.join("gen", dd_path)

def get_gen_dot_dfy_path(vad_path):
    assert vad_path.endswith(".vad")
    assert vad_path.startswith("code")
    dfy_path = vad_path.replace("code", "gen")
    return dfy_path.replace(".vad", ".dfy")

def get_dfy_files(include_gen):
    dfy_files = list()
    for root, _, files in os.walk("."):
        # do not include files in ./gen unless specified
        if  root.startswith("./gen") and not include_gen:
            continue
        for file in files:
            if file.endswith(".dfy"):
                dfy_path = os.path.relpath(os.path.join(root, file))
                dfy_files.append(dfy_path)
    return dfy_files

vad_include_pattern = re.compile('include\s+"(.+vad)"')

def get_vad_dependencies(vad_path):
    # print("[WARNING] .vad transitive dependencies not included")
    vad_path = os.path.relpath(vad_path)
    vad_dir = os.path.dirname(vad_path)
    # print(vad_dir)
    
    vad_dependencies = []
    f = open(vad_path)
    for line in f:
        line = line.strip()
        if line == "#verbatim":
            break
        match = re.search(vad_include_pattern, line)
        if match:
            included = os.path.join(vad_dir, match.group(1))
            included = get_gen_dot_dfy_path(included)
            vad_dependencies.append(included)
    return vad_dependencies 

def generate_dot_ninja():
    version = subprocess.run("ninja --version", shell=True, stdout=PIPE).stdout
    version = version.decode("utf-8").strip()
    if version != "1.10.1":
        print("[WARNING] ninja not found or uexpected version: " + version)

    # collect none generated .dfy
    dfy_files = get_dfy_files(False)
    code_dir = "code"

    # build .dfy from .vad 
    for file in os.listdir(code_dir):
        if file.endswith(".vad"):
            vad_path = os.path.join(code_dir, file)
            dfy_path = get_gen_dot_dfy_path(vad_path)
            vad_deps = get_vad_dependencies(vad_path)
            vad_deps = " ".join(vad_deps)
            ninja_content.append(f"build {dfy_path}: vale {vad_path} | {vad_deps}\n")
            dfy_files.append(dfy_path)

    # build .ver from .dfy
    for dfy_file in dfy_files:
        ver_path = get_dot_ver_path(dfy_file)
        dd_path = get_dot_dd_path(dfy_file)

        ninja_content.append(f"build {dd_path}: dfydep {dfy_file}\n")
        ninja_content.append(f"build {ver_path}: dafny {dfy_file} || {dd_path}")
        ninja_content.append(f"    dyndep = {dd_path}\n")

    with open(oupt_file_name, "w") as f:
        for line in ninja_content:
            f.write(line + "\n")

def generate_dot_dd(dfy_file):
    dfy_file = os.path.relpath(dfy_file)

    command = "dafny /printIncludes:Immediate %s" % dfy_file
    outputs = subprocess.run(command, shell=True, stdout=PIPE).stdout
    outputs = outputs.decode("utf-8")

    result = "ninja_dyndep_version = 1\n"
    result += "build " + get_dot_ver_path(dfy_file) + " : dyndep"

    if outputs == "":
        sys.exit()
    outputs = outputs.splitlines()[0].split(";")
    includes = []

    for (i, include) in enumerate(outputs):
        include = os.path.relpath(include)
        if i == 0:
            assert include == dfy_file
        else:
            include = get_dot_ver_path(include)
            includes.append(include)

    result += " | " + " ".join(includes)
    print(result)

def verify_dafny_proc(proc):
    dfy_files = get_dfy_files(True)
    command = 'grep -e "\(method\|function\|lemma\|predicate\).%s" -l ' % proc + " ".join(dfy_files)
    outputs = subprocess.run(command, shell=True, stdout=PIPE).stdout
    outputs = outputs.decode("utf-8")
    proc = proc.replace("_", "__")

    for dfy_file in outputs.splitlines():
        print("verify %s in %s" % (proc, dfy_file))
        command = "time -p dafny /compile:0 /proc:*%s " % proc + dfy_file
        # r = subprocess.check_output(command, shell=True).decode("utf-8")
        process = Popen(command, shell=True, stdout=PIPE)
        output = process.communicate()[0].decode("utf-8")
        print(output)

def verify_single_file(target):
    if not os.path.exists(target):
        return
    generate_dot_ninja()
    target  = os.path.relpath(target)
    if target.endswith(".dfy"):
        target = get_dot_ver_path(target)
        os.system("ninja -v " + target)
    elif target.endswith(".vad"):
        target = get_gen_dot_dfy_path(target)
        target = get_dot_ver_path(target)
        # print(target)
        os.system("ninja -v " + target)

def main():
    # build everything
    if len(sys.argv) == 1:
        generate_dot_ninja()
        os.system("ninja -v -j 4")
        return

    option = sys.argv[1]
    if option == "ver":
        verify_single_file(sys.argv[2])
    elif option == "dfydep":
        generate_dot_dd(sys.argv[2])
    elif option == "proc":
        verify_dafny_proc(sys.argv[2])
    elif option == "clean":
        os.system("rm -r ./gen")
        os.system("rm " + oupt_file_name)

if __name__ == "__main__":
    main()
