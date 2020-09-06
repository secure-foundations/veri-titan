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

print("\nrunning boolector")
os.system("python boolector.py %d | python filter.py > %s" % (full_bits, cnf_file))

print("\nrunning picosat")
os.system("picosat %s -t %s" % (cnf_file, trace_file))

l = open(cnf_file).readline().strip()
l = l.split()

print("\nreading trace")
f = open(trace_file)
cg_out = open(dot_file, "w+")
resolution_steps = 0

cg_out.write("digraph D {\n")
for line in f:
	if "*" not in line:
		continue
	line = line.strip().split()[:-1]
	start = line[0]
	for end in line[2:]:
		cg_out.write("\t{} -> {}\n".format(start, end))
	resolution_steps += 1
cg_out.write("}\n")

cg_out.close()

if resolution_steps < 100:
	os.system("dot -Tpng %s -o %s" % (dot_file, png_file))
else:
	print("too many steps skipping graph generation")

print("\ndumping stats")
print("variables: %s" % l[2])
print("clauses: %s" % l[3])
print("proof steps: %d" % resolution_steps)