import sys, os, subprocess,re
from subprocess import PIPE, Popen

rules = """
rule dafny
    command = dafny $in /compile:0 /timeLimit:20 /vcsCores:2 && touch $out

rule vale
    command = vale -dafnyText -in $in -out $out

rule dd-gen
    command = python3 build.py dd-gen $in > $out

rule dll-gen
    command = python3 build.py dll-gen $in

rule dll-run
    command = dotnet $in > $out

rule otbn-as
    command = otbn-as $in -o $out

rule otbn-ld
    command = otbn-ld $in -o $out
"""

PRINTER_DFY_PATH = "print.dfy"
PRINTER_DLL_PATH = "gen/print.dll"
PRINTER_CONFIG_PATH = "gen/print.runtimeconfig.json"

OUTPUT_ASM_PATH = "gen/output.s"
TEST_ASM_PATH = "run_modexp.s"
OUTPUT_ELF_PATH = "gen/run_modexp.elf"

NINJA_PATH = "build.ninja"
CODE_DIR = "code"

## misc utils

# run command

def os_system(command):
    print(command)
    os.system(command)

# convert path

def get_ver_path(dfy_path):
    dfy_path = os.path.relpath(dfy_path)
    ver_path = dfy_path.replace(".dfy", ".ver")
    if ver_path.startswith("gen"):
        return ver_path
    else:
        return os.path.join("gen", ver_path)

def get_dd_path(dfy_path):
    dfy_path = os.path.relpath(dfy_path)
    dd_path = dfy_path.replace(".dfy", ".dd")
    if dd_path.startswith("gen"):
        return dd_path
    else:
        return os.path.join("gen", dd_path)

def get_gen_dfy_path(vad_path):
    assert vad_path.endswith(".vad")
    assert vad_path.startswith("code")
    dfy_path = vad_path.replace("code", "gen")
    return dfy_path.replace(".vad", ".dfy")

def get_o_path(asm_path):
    asm_path = os.path.relpath(asm_path)
    assert asm_path.endswith(".s")
    if not asm_path.startswith("gen"):
        asm_path = "gen/" + asm_path
    return asm_path.replace(".s", ".o")

# list dependecy 

VAD_INCLUDE_PATTERN = re.compile('include\s+"(.+vad)"')

def list_vad_deps(vad_path):
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
        match = re.search(VAD_INCLUDE_PATTERN, line)
        if match:
            included = os.path.join(vad_dir, match.group(1))
            included = get_gen_dfy_path(included)
            vad_dependencies.append(included)
    return " ".join(vad_dependencies)

def list_dfy_deps(dfy_file):
    command = "dafny /printIncludes:Immediate %s" % dfy_file
    outputs = subprocess.run(command, shell=True, stdout=PIPE).stdout
    outputs = outputs.decode("utf-8")

    if outputs == "":
        return ""
    outputs = outputs.splitlines()[0].split(";")
    includes = []

    for (i, include) in enumerate(outputs):
        include = os.path.relpath(include)
        if i == 0:
            pass
            # assert include == dfy_file
        else:
            include = get_ver_path(include)
            includes.append(include)
    return " ".join(includes)

# list files

def get_dfy_files(include_gen):
    dfy_files = list()
    for root, _, files in os.walk("."):
        # do not include files in ./gen unless specified
        if  root.startswith("./gen") and not include_gen:
            continue
        for file in files:
            if file.endswith(".dfy"):
                if file == PRINTER_DFY_PATH:
                    continue
                dfy_path = os.path.relpath(os.path.join(root, file))
                dfy_files.append(dfy_path)
    return dfy_files

## main command (build)

class Generator():
    def __init__(self):
        version = subprocess.run("ninja --version", shell=True, stdout=PIPE).stdout
        version = version.decode("utf-8").strip()
        if version != "1.10.1":
            print("[WARNING] ninja not found or uexpected version: " + version)

        self.content = [rules]
        # collect none generated .dfy first
        self.dfy_files =get_dfy_files(False)

        self.generate_rules()
        self.write_ninja()

    def generate_vad_rules(self, vad_path):
        dfy_path = get_gen_dfy_path(vad_path)
        vad_deps = list_vad_deps(vad_path)
        self.content.append(f"build {dfy_path}: vale {vad_path} | {vad_deps}\n")
        # need to add this generated file as well
        self.dfy_files.append(dfy_path)

    def generate_dfy_rules(self, dfy_file):
        ver_path = get_ver_path(dfy_file)
        dd_path = get_dd_path(dfy_file)

        self.content.append(f"build {dd_path}: dd-gen {dfy_file}\n")
        self.content.append(f"build {ver_path}: dafny {dfy_file} || {dd_path}")
        self.content.append(f"    dyndep = {dd_path}\n")

    def generate_pinter_rules(self):
        printer_deps = list_dfy_deps(PRINTER_DFY_PATH)
        self.content.append(f"build {PRINTER_DLL_PATH}: dll-gen {PRINTER_DFY_PATH} | {printer_deps}\n")
        self.content.append(f"build {OUTPUT_ASM_PATH}: dll-run {PRINTER_DLL_PATH} \n")

    def generate_elf_rules(self):
        output_o_path = get_o_path(OUTPUT_ASM_PATH)
        self.content.append(f"build {output_o_path}: otbn-as {OUTPUT_ASM_PATH}\n")
        test_o_path = get_o_path(TEST_ASM_PATH)
        self.content.append(f"build {test_o_path}: otbn-as {TEST_ASM_PATH}\n")
        self.content.append(f"build {OUTPUT_ELF_PATH}: otbn-ld {test_o_path} {output_o_path}\n")

    def generate_rules(self):
        # rules to build .dfy from .vad 
        for file in os.listdir(CODE_DIR):
            if file.endswith(".vad"):
                vad_path = os.path.join(CODE_DIR, file)
                self.generate_vad_rules(vad_path)

        # rules to build .ver from .dfy
        for dfy_file in self.dfy_files:
            self.generate_dfy_rules(dfy_file)

        # rules for the printer
        self.generate_pinter_rules()

        # rules for the elf
        self.generate_elf_rules()

    def write_ninja(self):
        with open(NINJA_PATH, "w") as f:
            for line in self.content:
                f.write(line + "\n")

## separate command: dd-gen

def generate_dd(dfy_file):
    dfy_file = os.path.relpath(dfy_file)

    result = "ninja_dyndep_version = 1\n"
    result += "build " + get_ver_path(dfy_file) + "  : dyndep"

    outputs = list_dfy_deps(dfy_file)

    if outputs == "":
        sys.exit()

    print(result + " | " + outputs)

## separate command: proc

def verify_dafny_proc(proc):
    dfy_files = get_dfy_files(True)
    command = 'grep -e "\(method\|function\|lemma\|predicate\).%s" -l ' % proc + " ".join(dfy_files)
    outputs = subprocess.run(command, shell=True, stdout=PIPE).stdout
    outputs = outputs.decode("utf-8")
    proc = proc.replace("_", "__")

    for dfy_file in outputs.splitlines():
        print("verify %s in %s" % (proc, dfy_file))
        command = "time -p dafny /trace /timeLimit:20 /compile:0 /proc:*%s " % proc + dfy_file
        # r = subprocess.check_output(command, shell=True).decode("utf-8")
        process = Popen(command, shell=True, stdout=PIPE)
        output = process.communicate()[0].decode("utf-8")
        print(output)

## separate command: ver

def verify_single_file(target):
    if not os.path.exists(target):
        return
    generate_dot_ninja()
    target  = os.path.relpath(target)
    if target.endswith(".dfy"):
        target = get_ver_path(target)
        os.system("ninja -v " + target)
    elif target.endswith(".vad"):
        target = get_gen_dfy_path(target)
        target = get_ver_path(target)
        # print(target)
        os.system("ninja -v " + target)

## separate command: dll-gen

def generate_print_dll(dfy_path):
    # ninja sanity check
    assert dfy_path == PRINTER_DFY_PATH 
    command = f"dafny {PRINTER_DFY_PATH} /compile:1 /vcsCores:2 /out:temp.dll"
    command += f" && mv temp.dll {PRINTER_DLL_PATH} && mv temp.runtimeconfig.json {PRINTER_CONFIG_PATH}"
    os_system(command)

## separate command: elf-gen
def generate_elf(asm_path):
    # ninja sanity check
    assert asm_path == OUTPUT_ASM_PATH
    command()
    # command = f"dafny {PRINTER_DFY_PATH} /compile:1 /vcsCores:2 /out:temp.dll"
    # print(command)
    # os_system(command)
# TEST_ASM_PATH


## command line interface

def main():
    # build everything
    if len(sys.argv) == 1:
        g = Generator()
        # os.system("ninja -v -j 4")
        return

    option = sys.argv[1]
    if option == "ver":
        verify_single_file(sys.argv[2])
    elif option == "proc":
        verify_dafny_proc(sys.argv[2])
    elif option == "dd-gen":
        generate_dd(sys.argv[2])
    elif option == "dll-gen":
        generate_print_dll(sys.argv[2])
    elif option == "clean":
        os.system("rm -r ./gen")
        os.system("rm " + NINJA_PATH)

if __name__ == "__main__":
    main()
