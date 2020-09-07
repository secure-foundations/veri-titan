import sys, os

try:
	func_name = sys.argv[1]
	full_bits = int(sys.argv[2])
except:
	print("usage: python orchestrate.py [function_name] [bit_number]")
	sys.exit()

print("using %d bit width" % full_bits)

if not os.path.exists("gen"):
	os.makedirs("gen")

name = "gen/%s_%d" % (func_name, full_bits)
smt_file = name + ".smt2"
cnf_file = name + ".cnf"
trace_file = name + ".trace"
dot_file = name + ".dot"
png_file = name + ".png"

print("\nexporting smt query")
if os.system("python bv_exprs.py %s %d | tail -n +2 > %s" % (func_name, full_bits, smt_file)) != 0:
	print("smt export failed")
	sys.exit(1)

print("running boolector")

if os.system("boolector %s -dd | python filter.py > %s" % (smt_file, cnf_file)) != 0:
	print("cnf export failed")
	sys.exit(1)

print("running picosat")
r = os.system("picosat %s -t %s" % (cnf_file, trace_file))

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