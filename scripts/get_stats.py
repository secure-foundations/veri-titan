import sys
import re
import os

def get_ins_stats(path):
    source = open(path)
    pattern = re.compile("^([A-Z.]+) ")
    bn_ins = set()
    bn_ins_count = 0

    none_bn_ins = set()
    none_bn_ins_count = 0

    procedure_count = 0

    for line in source.readlines():
        line = line.strip()

        if line.endswith(":"):
            procedure_count += 1
        else:
            match = re.match(pattern, line)
            if match:
                ins = match.group(0)
                if ins.startswith("BN"): 
                    bn_ins_count += 1
                    bn_ins.add(ins)
                else:
                    none_bn_ins_count += 1
                    none_bn_ins.add(ins)
    source.close()
    print("# procedures: %d" % procedure_count)
    print("# bn instructions: %d" % bn_ins_count)
    print("# unique bn instructions: %d" % len(bn_ins))
    print("# none bn instructions: %d" % none_bn_ins_count)
    print("# unique none bn instructions: %d" % len(none_bn_ins))

def build_call_graph(path):
    source = open(path)
    callees = dict()
    cur_set = None

    pattern = re.compile("^jal (.+), ([^\s-]+)")
    funciton_pattern = re.compile("^([a-z0-9A-Z_]+):")

    for line in source.readlines():
        line = line.strip()
        match = re.match(funciton_pattern, line)

        if match:
            cur_func = match.group(1)
            callees[cur_func] = set()
            cur_set = callees[cur_func]

        match = re.match(pattern, line)
        if match:
            callee = match.group(2)
            cur_set.add(callee)
    source.close()

    content = "digraph D {\n"
    for k, v in callees.items():
        for f in v:
            content += "\t{} -> {}\n".format(k, f)
    content += "}\n"

    cg_out = open("cg.dot", "w+")
    cg_out.write(content)
    cg_out.close()

    os.system("dot -Tpng cg.dot -o cg.png")

source = sys.argv[1]
build_call_graph(source)
# get_ins_stats(source)