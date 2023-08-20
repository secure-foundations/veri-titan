import fileinput

p = False

for line in fileinput.input():
    if "unknown" in line:
        line = line.replace("unknown\n", "")
    if "p cnf" in line:
        p = True
    if "c CNF dump 1 end" in line:
        p = False
    if p:
        print(line, end = '')