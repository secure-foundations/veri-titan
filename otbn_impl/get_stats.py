import sys
import re

source = open(sys.argv[1])
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

print("# procedures: %d" % procedure_count)
print("# bn instructions: %d" % bn_ins_count)
print("# unique bn intruction: %d" % len(bn_ins))
print("# none bn instructions: %d" % none_bn_ins_count)
print("# unique none bn intruction: %d" % len(none_bn_ins))