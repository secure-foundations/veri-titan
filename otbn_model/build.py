import sys, os, subprocess
from subprocess import PIPE

rules = """
rule dafny
    command = dafny /compile:0 /nologo $in && touch $out

rule vale
    command = vale.exe -dafnyText -in $in -out $out

rule ddep
    command = python build.py ddep $in > $out
"""

ninja_out = [rules]

def get_ver_path(dfy_path):
    # assuming there aren't duplicated names
    return "./gen/" + dfy_path.split("/")[-1] + ".ver"

def get_dd_path(dfy_path):
    # assuming there aren't duplicated names
    return "./gen/" + dfy_path.split("/")[-1] + ".dd"

def get_dfy_files(exclude_gen):
    dfy_files = list()
    for root, dirs, files in os.walk("."):
        # print(dirs)
        if root == "./gen" and exclude_gen:
            continue
        for file in files:
            if file.endswith(".dfy"):
                dfy_files.append(os.path.join(root, file))
    return dfy_files

def gen_ninja():
    dfy_files = get_dfy_files(True)

    for file in os.listdir("./code"):
        if file.endswith(".vad"):
            # if any vad file is updated, generate the dfy file (no verification)
            vad_file = os.path.join("./code", file)
            file = file.replace(".vad", ".dfy")
            dfy_file = os.path.join("./gen", file)
            dfy_files.append(dfy_file)
            ninja_out.append(f"build {dfy_file}: vale {vad_file}\n")

    for dfy_file in dfy_files:
        ver_path = get_ver_path(dfy_file)
        dd_path = get_dd_path(dfy_file)

        ninja_out.append(f"build {dd_path}: ddep {dfy_file}\n")
        ninja_out.append(f"build {ver_path}: dafny {dfy_file} || {dd_path}")
        ninja_out.append(f"    dyndep = {dd_path}\n")
    
    with open("build.ninja", "w") as f:
        for line in ninja_out:
            f.write(line + "\n")

if len(sys.argv) == 1:
    version = subprocess.run("ninja --version", shell=True, stdout=PIPE).stdout
    version = version.decode("utf-8").strip()
    if version != "1.10.1":
        print("[WARNING] ninja not found or uexpected version: " + version)
    gen_ninja()
    os.system("ninja -v")
    sys.exit()

option = sys.argv[1]
if option == "ddep":
    dfy_file = sys.argv[2] 
    command = "dafny /printIncludes:Immediate %s" % dfy_file
    outputs = subprocess.run(command, shell=True, stdout=PIPE).stdout
    outputs = outputs.decode("utf-8")

    result = "ninja_dyndep_version = 1\n"
    result += "build " + get_ver_path(dfy_file) + " : dyndep"
    if outputs != "":
        includes = outputs.splitlines()[0]
        includes = includes.split(";")
        assert includes[0] == dfy_file
        result += " | " + " ".join([get_ver_path(i) for i in includes[1:]])
    print(result)
elif option == "proc":
    proc = sys.argv[2]
    dfy_files = get_dfy_files(False)
    command = 'grep -e "\(method\|function\|lemma\|predicate\).%s" -l ' % proc + " ".join(dfy_files)
    outputs = subprocess.run(command, shell=True, stdout=PIPE).stdout
    outputs = outputs.decode("utf-8")
    proc = proc.replace("_", "__")

    for dfy_file in outputs.splitlines():
        print("verify %s in %s" % (proc, dfy_file))
        command = "time -p dafny /compile:0 /nologo /proc:*%s " % proc + dfy_file
        r = subprocess.check_output(command, shell=True).decode("utf-8")
        print(r)