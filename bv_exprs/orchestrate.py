import sys, os

try:
	full_bits = int(sys.argv[1])
except:
	print("usage: python orchestrate.py [bit_number]")
	full_bits = 2

print("using %d bit width" % full_bits)

if not os.path.exists("gen"):
	os.makedirs("gen")

name = "gen/%d_bits" % full_bits
cnf_file = name + ".cnf"
trace_file = name + ".trace"
dot_file = name + ".dot"
png_file = name + ".png"

os.system("python boolector.py %d | tail -n +4 | head -n -1 > %s" % (full_bits, cnf_file))
os.system("picosat %s -t %s" % (cnf_file, trace_file))

l = open(cnf_file).readline().strip()
l = l.split()
print("variables: %s" % l[2])
print("clauses: %s" % l[3])

# os.system("head -n 1 %s" % cnf_file)

f = open(trace_file)
resolution_steps = 0

content = "digraph D {\n"
for line in f:
	if "*" not in line:
		continue
	line = line.strip().split()[:-1]
	start = line[0]
	for end in line[2:]:
		content += "\t{} -> {}\n".format(start, end)
	resolution_steps += 1
content += "}\n"

cg_out = open(dot_file, "w+")
cg_out.write(content)
cg_out.close()

os.system("dot -Tpng %s -o %s" % (dot_file, png_file))

print("proof steps: %d" % resolution_steps)