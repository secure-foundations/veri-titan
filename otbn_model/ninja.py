import os, subprocess

rules = """
rule dafny
    command = dafny /compile:0 /nologo $in && touch $out

rule vale
    command = vale.exe -dafnyText -in $in -out $out

rule ddep
    command = python dfy_dep.py $in > $out
"""

if not os.path.exists("./gen"):
    os.makedirs("./gen")

print(rules)

def get_ver_path(dfy_path):
    # assuming there aren't duplicated names
    return "./gen/" + dfy_path.split("/")[-1] + ".ver"

def get_dd_path(dfy_path):
    # assuming there aren't duplicated names
    return "./gen/" + dfy_path.split("/")[-1] + ".dd"

def get_dfy_files():
    dfy_files = list()
    for root, dirs, files in os.walk("."):
        if root == "./gen":
            continue
        for file in files:
            if file.endswith(".dfy"):
                dfy_files.append(os.path.join(root, file))
    return dfy_files

dfy_files = get_dfy_files()

for file in os.listdir("./code"):
    if file.endswith(".vad"):
        # if any vad file is updated, generate the dfy file (no verification)
        vad_file = os.path.join("./code", file)
        file = file.replace(".vad", ".dfy")
        dfy_file = os.path.join("./gen", file)
        dfy_files.append(dfy_file)
        print(f"build {dfy_file}: vale {vad_file}\n")

for dfy_file in dfy_files:
    ver_path = get_ver_path(dfy_file)
    dd_path = get_dd_path(dfy_file)

    print(f"build {dd_path}: ddep {dfy_file}\n")
    print(f"build {ver_path}: dafny {dfy_file} || {dd_path}")
    print(f"    dyndep = {dd_path}\n")