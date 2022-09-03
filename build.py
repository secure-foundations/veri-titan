#!/usr/bin/env python

import sys, os, subprocess, re, platform
from subprocess import PIPE, Popen
from os.path import exists

TOOLS_DIR = "./tools"
DAFNY_PATH = "./tools/dafny/Binaries/Dafny"
VALE_PATH = "./tools/vale/bin/vale"
DAFNY_LIB_DIR = "./std_lib"

DAFNY_LIB_HASH = "6ce420782487e592dd9925acf715e0d9548bc300"

# DAFNY_ZIP_LINUX = "dafny-3.0.0-x64-ubuntu-16.04.zip"
# DAFNY_ZIP_MACOS = "dafny-3.0.0-x64-osx-10.14.2.zip"

def rules():
    vale = "" if platform.system() == "Linux" else "mono"
    vale += " " + VALE_PATH

    return f"""
rule dafny
    command = {DAFNY_PATH} /compile:0 /noNLarith /timeLimit:20 /vcsCores:4 $in && touch $out

rule dafny-nl
    command = {DAFNY_PATH} /compile:0 /timeLimit:20 /vcsCores:4 $in && touch $out

rule vale
    command = {vale} -dafnyText -in $in -out $out

rule dd-gen
    command = python3 build.py dd-gen $in $out

rule dll-gen
    command = python3 build.py dll-gen $in $out

rule dll-run
    command = dotnet $in > $out

rule otbn-as
    command = otbn_as.py $in -o $out

rule otbn-ld
    command = otbn_ld.py $in -o $out
"""

OTBN_ASM_PATH = "gen/otbn_modexp.s"
RISCV_ASM_PATH = "gen/riscv_modexp.s"
OTBN_TEST_ASM_PATH = "ref/run_modexp.s"
OUTPUT_ELF_PATH = "gen/run_modexp.elf"

DLL_SOURCES = {
    "spec/arch/otbn/modexp_printer.s.dfy": OTBN_ASM_PATH,
    "spec/arch/otbn/simulator.i.dfy": "gen/arch/otbn/sim.out", 
    "spec/arch/riscv/printer.s.dfy": RISCV_ASM_PATH,
}

NINJA_PATH = "build.ninja"
CODE_DIRS = ["spec", "impl", "glue", "misc"]
GEN_DIR = "gen"

NL_FILES = {"lib/sub_mod_nl_lemmas.i.dfy"}

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
    os_type = platform.system()

    # ninja
    version = subprocess_run("ninja --version")
    if not version.startswith("1.10."):
        print("[WARN] ninja not found or unexpected version.  Expected 1.10.*, found: " + version)

    # dotnet
    version = subprocess_run("dotnet --list-sdks")
    if "5.0" not in version:
        print("[WARN] dotnet not found or unexpected version. Expected 5.0, found: " + version)
    else:
        print("[INFO] Found dotnet version: " + version)

    # nuget
    version = subprocess_run("nuget help | grep -m 1 Version")
    if "5.5" not in version:
        print("[WARN] nuget not found or unexpected version.  Expected 5.5, found: " + version)
    else:
        print("[INFO] Found nuget version: " + version)

    # C# compiler (Vale)
    path = subprocess_run("which dmsc")
    if "dmsc" not in path:
        # Check for mcs (mono C# compiler) instead
        path = subprocess_run("which mcs")
        if "mcs" not in path:
            print("[WARN] C# compiler (dmsc or mcs - Vale dependency) not found")
        else:
            print("[INFO] mcs (Vale dependency) found")
    else:
        print("[INFO] dmsc (Vale dependency) found")

    # scons (Vale)
    path = subprocess_run("which scons")
    if "scons" not in path:
        print("[WARN] scons (Vale dependency) not found")
    else:
        print("[INFO] scons (Vale dependency) found")

    # F# compiler (Vale)
    path = subprocess_run("which fsharpc")
    if "fsharpc" not in path:
        print("[WARN] fsharpc (Vale dependency) not found")
    else:
        print("[INFO] fsharpc (Vale dependency) found")

    path = subprocess_run("which otbn_as.py")
    if "otbn_as.py" not in path:
        print("[WARN] otbn_as.py not found")
    else:
        print("[INFO] otbn_as.py found")

    path = subprocess_run("which otbn_ld.py")
    if "otbn_ld.py" not in path:
        print("[WARN] otbn_ld.py not found")
    else:
        print("[INFO] otbn_ld.py found")

    while 1:
        print("confirm dependecies are installed [y/n] ", end='')
        choice = input().lower()
        if choice == "n":
            return
        elif choice == "y":
            break

    if not os.path.exists(TOOLS_DIR):
        os.mkdir(TOOLS_DIR)

    z3_target = "z3-ubuntu" if os_type == "Linux" else "z3-mac"
    if os.path.exists(DAFNY_PATH):
        print("[INFO] dafny binary already exists")
    else:
        os.system("cd tools && git clone git@github.com:secure-foundations/dafny.git")
        os.system(f"cd tools/dafny && git checkout groebner-extension && make exe && make {z3_target}")

    if os.path.exists(VALE_PATH):
        print("[INFO] vale binary already exists")
    else:
        os.system("cd tools && git clone git@github.com:project-everest/vale.git")
        os.system("cd tools/vale && git checkout otbn-custom && bash ./run_scons.sh")
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
        if "std_lib" in include:
            continue
        if i == 0:
            # print(dfy_file)
            continue
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

    def generate_dll_rules(self):
        for dafny_path, dll_out_path in DLL_SOURCES.items():
            dfy_deps = list_dfy_deps(dafny_path)
            dll_path = get_dll_path(dafny_path)
            self.content.append(f"build {dll_path}: dll-gen {dafny_path} | {dfy_deps}\n")
            self.content.append(f"build {dll_out_path}: dll-run {dll_path} \n")

    def generate_elf_rules(self):
        output_o_path = get_o_path(OTBN_ASM_PATH)
        self.content.append(f"build {output_o_path}: otbn-as {OTBN_ASM_PATH}\n")
        test_o_path = get_o_path(OTBN_TEST_ASM_PATH)
        self.content.append(f"build {test_o_path}: otbn-as {OTBN_TEST_ASM_PATH}\n")
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
        self.generate_dll_rules()

        # rules for the elf
        self.generate_elf_rules()

    def write_ninja(self):
        with open(NINJA_PATH, "w") as f:
            for line in self.content:
                f.write(line + "\n")

    def __init__(self):
        self.content = [rules()]
        # collect none generated .dfy first
        self.dfy_files = get_dfy_files(False)

        self.generate_rules()
        self.write_ninja()

# ## separate command: dd-gen

def generate_dd(dfy_file, dd_file):
    dfy_file = os.path.relpath(dfy_file)

    result = "ninja_dyndep_version = 1\n"
    result += "build " + get_ver_path(dfy_file) + "  : dyndep"
    outputs = list_dfy_deps(dfy_file)

    open(dd_file, "w").write(result + " | " + outputs + "\n")

## separate command: proc

def verify_dafny_proc(proc):
    dfy_files = get_dfy_files(True)
    command = 'grep -e "\(method\|function\|lemma\|predicate\).%s" -l ' % proc + " ".join(dfy_files)
    outputs = subprocess.run(command, shell=True, stdout=PIPE).stdout
    outputs = outputs.decode("utf-8")
    proc = proc.replace("_", "__")

    for dfy_file in outputs.splitlines():
        print("verify %s in %s" % (proc, dfy_file))
        command = f"time -p {DAFNY_PATH} /trace /timeLimit:20 /noNLarith /compile:0 /proc:*%s " % proc + dfy_file
        # r = subprocess.check_output(command, shell=True).decode("utf-8")
        process = Popen(command, shell=True, stdout=PIPE)
        output = process.communicate()[0].decode("utf-8")
        print(output)

## separate command: ver

def verify_single_file(target):
    if not os.path.exists(target):
        return
    target = os.path.relpath(target)
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
    output_dir, dll_name = os.path.split(dll_path)
    json_name = dll_name.replace(".dll", ".runtimeconfig.json")
    json_path = output_dir + "/" + json_name
    command = f"{DAFNY_PATH} /compile:1 /spillTargetCode:1 /noNLarith /vcsCores:2 {dfy_path} /out:{dll_path}"
    print(command)
    output = subprocess_run(command)
    print(output)
    # os.system(f"mv {dll_name} {dll_path}")
    # os.system(f"mv {json_name} {json_path}")

def replace_string_file(file_path, src, dst):
    # print(file_path)
    with open(file_path) as f:
        filedata = f.read()
        # Replace the target string
    filedata = filedata.replace(src, dst)
    with open(file_path, 'w') as f:
        f.write(filedata)
  
def replace_string(src, dst):
    target_dirs = set(CODE_DIRS)

    for root, _, files in os.walk("."):
        tpl = "." if root == "." else root.split("/")[1]
        if tpl not in target_dirs:
            continue
        for file in files:
            file_path = os.path.relpath(os.path.join(root, file))
            replace_string_file(file_path, src, dst)

## command line interface

def main():
    # build everything
    if len(sys.argv) == 1:
        g = Generator()
        print("Wrote out build.ninja.  Now run: ninja -v -j4")
        # os.system("ninja -v -j 4")
        return

    option = sys.argv[1]
    if option == "ver":
        verify_single_file(sys.argv[2])
    elif option == "proc":
        verify_dafny_proc(sys.argv[2])
    elif option == "dd-gen":
        generate_dd(sys.argv[2], sys.argv[3])
    elif option == "dll-gen":
        generate_dll(sys.argv[2], sys.argv[3])
    elif option == "clean":
        os.system(f"rm -r gen/spec gen/impl gen/glue gen/misc")
        os.system("rm " + NINJA_PATH)
    elif option == "setup":
        setup_tools()
    elif option == "replace":
        replace_string(sys.argv[2], sys.argv[3])

if __name__ == "__main__":
    main()
