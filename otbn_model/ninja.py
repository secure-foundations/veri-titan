import os, subprocess
from subprocess import PIPE

rules = """
rule dafny
    command = dafny /compile:0 /nologo $in && touch $out

rule vale
    command = vale.exe -dafnyText -in $in -out $out

rule dafny-dep
    command = python dfy_dep.py $in >> $out
"""

if not os.path.exists("./gen"):
    os.makedirs("./gen")

print(rules)

def get_ver_path(dfy_path):
    # assuming there aren't duplicated names
    return "./gen/" + dfy_path.split("/")[-1] + ".ver"

# def get_dfy_includes(dfy_file):
#     command = "dafny /printIncludes:Immediate %s" % dfy_file
#     outputs = subprocess.run(command, shell=True, stdout=PIPE).stdout
#     outputs = outputs.decode("utf-8")
#     if outputs == "":
#         return []
#     includes = outputs.splitlines()[0]
#     includes = includes.split(";")
#     return includes

def get_dfy_files():
    dfy_files = list()
    for root, dirs, files in os.walk("."):
        for file in files:
            if file.endswith(".dfy"):
                dfy_files.append(os.path.join(root, file))
    return dfy_files

# def verify_rec(dfy_file):
#     ver_path = get_ver_path(dfy_file)
#     print(ver_path)
    # includes = get_dfy_includes(dfy_file)

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
    # print(ver_path)
    print(f"build {ver_path}: dafny {dfy_file}\n")

    # for path in includes:
        # dep_ver_path = get_ver_path(path)
        # if dep_ver_path == ver_path:
            # continue
        # env.Dafny(dep_ver_path, path)
        # print(dep_ver_path)
        # env.Depends(ver_path, dep_ver_path)

# build gen/d0inv.dfy: vale code/d0inv.vad
