import sys, os, subprocess, re
from subprocess import PIPE, Popen
from os.path import exists

TOOLS_DIR = "./tools"
DAFNY_PATH = "./tools/dafny/dafny"
VALE_PATH = "./tools/vale/bin/vale"
DAFNY_LIB_DIR = "./std_lib"

DAFNY_LIB_HASH = "84d160538b6442017a5401feb91265147bf34bfc"

rules = f"""
rule dafny
    command = {DAFNY_PATH} /compile:0 /noNLarith /timeLimit:20 /vcsCores:2 $in && touch $out

rule dafny-nl
    command = {DAFNY_PATH} /compile:0 /timeLimit:20 /vcsCores:2 $in && touch $out

rule vale
    command = {VALE_PATH} -dafnyText -in $in -out $out

rule dd-gen
    command = python3 build.py dd-gen $in > $out

rule dll-gen
    command = python3 build.py dll-gen $in $out

rule dll-run
    command = dotnet $in > $out

rule otbn-as
    command = otbn-as $in -o $out

rule otbn-ld
    command = otbn-ld $in -o $out
"""

OT_PRINTER_DFY_PATH = "arch/otbn/printer.s.dfy"
OT_SIMULATOR_DFY_PATH = "arch/otbn/simulator.i.dfy"
DLL_SOURCES = {OT_PRINTER_DFY_PATH, OT_SIMULATOR_DFY_PATH}

OUTPUT_ASM_PATH = "gen/arch/otbn/printer.s.dll.out"
TEST_ASM_PATH = "impl/otbn/run_modexp.s"
OUTPUT_ELF_PATH = "gen/impl/otbn/run_modexp.elf"

NINJA_PATH = "build.ninja"
CODE_DIRS = ["arch", "impl", "lib"]
GEN_DIR = "gen"


NL_FILES = {"arch/riscv/vale.i.dfy",
    "impl/riscv/mod32_lemmas.i.dfy"}

## misc utils

# run command

def os_system(command):
    print(command)
    code = os.system(command)
    sys.exit(code)

def subprocess_run(command, cwd=None):
    # print(command)
    output = subprocess.run(command, shell=True, stdout=PIPE, cwd=cwd).stdout
    return output.decode("utf-8").strip()

# convert path

def get_ver_path(dfy_path):
    dfy_path = os.path.relpath(dfy_path)
    ver_path = dfy_path.replace(".dfy", ".ver")
    if ver_path.startswith(GEN_DIR):
        return ver_path
    else:
        return os.path.join(GEN_DIR, ver_path)

def get_dd_path(dfy_path):
    dfy_path = os.path.relpath(dfy_path)
    dd_path = dfy_path.replace(".dfy", ".dd")
    if dd_path.startswith(GEN_DIR):
        return dd_path
    else:
        return os.path.join(GEN_DIR, dd_path)

def get_gen_dfy_path(vad_path):
    assert vad_path.endswith(".vad")
    dfy_path = os.path.join(GEN_DIR, vad_path)
    return dfy_path.replace(".vad", ".dfy")

def get_dll_path(dfy_path):
    dfy_path = os.path.relpath(dfy_path)
    dll_path = dfy_path.replace(".dfy", ".dll")
    assert(not dll_path.startswith(GEN_DIR))
    return os.path.join(GEN_DIR, dll_path)

def get_o_path(asm_path):
    asm_path = os.path.relpath(asm_path)
    # assert asm_path.endswith(".s")
    if not asm_path.startswith(GEN_DIR):
        asm_path = os.path.join(GEN_DIR, asm_path)
    return asm_path.replace(".s", ".o")

## separate command: setup

def setup_tools():
    # ninja
    version = subprocess_run("ninja --version")
    if version != "1.10.1":
        print("[WARN] ninja not found or uexpected version: " + version)
    # dotnet
    version = subprocess_run("dotnet --list-sdks")
    if "5.0" not in version:
        print("[WARN] dotnet not found or uexpected version: " + version)
    else:
        print("[INFO] dotnet version: " + version)

    # nuget
    version = subprocess_run("nuget help | grep Version")
    if "5.5" not in version:
        print("[WARN] nuget not found or uexpected version: " + version)
    else:
        print("[INFO] nuget version: " + version)

    path = subprocess_run("which otbn-as")

    if "otbn-as" not in path:
        print("[WARN] otbn-as not found")
    else:
        print("[INFO] otbn-as found")

    path = subprocess_run("which otbn-ld")

    if "otbn-ld" not in path:
        print("[WARN] otbn-ld not found")
    else:
        print("[INFO] otbn-ld found")

    while 1:
        print("confrim dependecies are installed [y/n] ", end='')
        choice = input().lower()
        if choice == "n":
            return
        elif choice == "y":
            break

    if not os.path.exists(TOOLS_DIR):
        os.mkdir(TOOLS_DIR)

    if os.path.exists(DAFNY_PATH):
        print("[INFO] dafny binary already exists")
    else:
        os.system("wget https://github.com/dafny-lang/dafny/releases/download/v3.0.0/dafny-3.0.0-x64-ubuntu-16.04.zip")
        os.system(f"unzip dafny-3.0.0-x64-ubuntu-16.04.zip -d {TOOLS_DIR}")
        os.system(f"rm dafny-3.0.0-x64-ubuntu-16.04.zip")

    if os.path.exists(VALE_PATH):
        print("[INFO] vale binary already exists")
    else:
        os.system("cd tools && git clone git@github.com:project-everest/vale.git")
        os.system("cd tools/vale && git checkout otbn-custom && ./run_scons.sh")
        os.system("mv tools/vale/bin/vale.exe tools/vale/bin/vale")

    if os.path.exists(DAFNY_LIB_DIR):
        print("[INFO] dafny library already exists")
    else:
        os.system(f"git clone git@github.com:secure-foundations/libraries.git {DAFNY_LIB_DIR} && cd {DAFNY_LIB_DIR} && git checkout {DAFNY_LIB_HASH}")

# list dependecy 

def list_dfy_deps(dfy_file):
    command = f"{DAFNY_PATH} /printIncludes:Immediate %s" % dfy_file
    outputs = subprocess.run(command, shell=True, stdout=PIPE).stdout
    outputs = outputs.decode("utf-8")

    if outputs == "":
        return ""
    outputs = outputs.splitlines()[0].split(";")
    includes = []

    for (i, include) in enumerate(outputs):
        include = os.path.relpath(include)
        if include.startswith(DAFNY_LIB_DIR):
            continue
        if i == 0:
            # print(dfy_file)
            pass
        else:
            include = get_ver_path(include)
            includes.append(include)
    return " ".join(includes)

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
            included = os.path.relpath(included)
            if not exists(included):
                print(f"[ERROR] {vad_path} is importing {included} that doesn't exist")
                sys.exit(-1)
            vad_dependencies.append(included)

            included = get_gen_dfy_path(included)
            vad_dependencies.append(included)

    return " ".join(vad_dependencies)

# list files

def get_dfy_files(include_gen):
    dfy_files = list()
    target_dirs = set(CODE_DIRS)

    # do not include files in ./gen unless specified
    if include_gen:
        target_dirs.add(GEN_DIR)

    # do not include special dfy files

    for root, _, files in os.walk("."):
        tpl = "." if root == "." else root.split("/")[1]
        if tpl not in target_dirs:
            continue
        for file in files:
            if file.endswith(".dfy"):
                dfy_path = os.path.relpath(os.path.join(root, file))
                if dfy_path in DLL_SOURCES:
                    continue
                dfy_files.append(dfy_path)
    return dfy_files

def get_vad_files():
    vad_files = list()
    target_dirs = set(CODE_DIRS)

    for root, _, files in os.walk("."):
        tpl = "." if root == "." else root.split("/")[1]
        if tpl not in target_dirs:
            continue
        for file in files:
            if file.endswith(".vad"):
                vad_path = os.path.relpath(os.path.join(root, file))
                vad_files.append(vad_path)
    return vad_files

## main command (build)

class Generator():
    def generate_vad_rules(self, vad_path):
        # print(vad_path)
        dfy_path = get_gen_dfy_path(vad_path)
        vad_deps = list_vad_deps(vad_path)
        # print(vad_path, dfy_path)
        self.content.append(f"build {dfy_path}: vale {vad_path} | {vad_deps}\n")
        # need to add this generated file as well
        self.dfy_files.append(dfy_path)

    def generate_dfy_rules(self, dfy_file):
        ver_path = get_ver_path(dfy_file)
        dd_path = get_dd_path(dfy_file)

        self.content.append(f"build {dd_path}: dd-gen {dfy_file}\n")
        if dfy_file in NL_FILES:
            self.content.append(f"build {ver_path}: dafny-nl {dfy_file} || {dd_path}")
        else:
            self.content.append(f"build {ver_path}: dafny {dfy_file} || {dd_path}")
        self.content.append(f"    dyndep = {dd_path}\n")

    def generate_dll_rules(self, dafny_path):
        dfy_deps = list_dfy_deps(dafny_path)
        dll_path = get_dll_path(dafny_path)
        self.content.append(f"build {dll_path}: dll-gen {dafny_path} | {dfy_deps}\n")
        dll_out_path = dll_path + ".out"
        self.content.append(f"build {dll_out_path}: dll-run {dll_path} \n")

    def generate_elf_rules(self):
        output_o_path = get_o_path(OUTPUT_ASM_PATH)
        self.content.append(f"build {output_o_path}: otbn-as {OUTPUT_ASM_PATH}\n")
        test_o_path = get_o_path(TEST_ASM_PATH)
        self.content.append(f"build {test_o_path}: otbn-as {TEST_ASM_PATH}\n")
        self.content.append(f"build {OUTPUT_ELF_PATH}: otbn-ld {test_o_path} {output_o_path}\n")

    def generate_rules(self):
        # rules to build .dfy from .vad 
        vad_files = get_vad_files()
        for vad_file in vad_files:
            # print(vad_file)
            self.generate_vad_rules(vad_file)

        # rules to build .ver from .dfy
        for dfy_file in self.dfy_files:
            self.generate_dfy_rules(dfy_file)

        # rules for the printer
        for dll_source in DLL_SOURCES:
            self.generate_dll_rules(dll_source)

        # rules for the elf
        self.generate_elf_rules()

    def write_ninja(self):
        with open(NINJA_PATH, "w") as f:
            for line in self.content:
                f.write(line + "\n")

    def __init__(self):
        self.content = [rules]
        # collect none generated .dfy first
        self.dfy_files = get_dfy_files(False)

        self.generate_rules()
        self.write_ninja()

# ## separate command: dd-gen

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
        command = f"time -p {DAFNY_PATH} /trace /timeLimit:20 /compile:0 /proc:*%s " % proc + dfy_file
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

def generate_dll(dfy_path, dll_path):
    dfy_path = os.path.realpath(dfy_path)
    assert(dll_path.startswith(GEN_DIR) and dll_path.endswith(".dll"))
    dll_dir = os.path.dirname(dll_path)
    command = f"dafny /compile:1 /noNLarith /vcsCores:2 {dfy_path} /out:{dll_path}"
    output = subprocess_run(command, cwd=dll_dir) 
    print(output)

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
        generate_dll(sys.argv[2], sys.argv[3])
    elif option == "clean":
        os.system(f"rm -r {GEN_DIR}")
        os.system("rm " + NINJA_PATH)
    elif option == "setup":
        setup_tools()

if __name__ == "__main__":
    main()
