import sys, os

try:
	func_name = sys.argv[1]
	full_bits = int(sys.argv[2])
except:
	print("usage: python test_proof.py [function_name] [bit_number]")
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

print("[1] exporting smt query")
if os.system("python bv_exprs.py %s %d | tail -n +2 > %s" % (func_name, full_bits, smt_file)) != 0:
	print("smt export failed")
	sys.exit(1)

print("[2] running boolector")

if os.system("boolector %s -dd | python filter.py > %s" % (smt_file, cnf_file)) != 0:
	print("cnf export failed")
	sys.exit(1)

print("[3] running picosat")
r = os.system("picosat %s -t %s" % (cnf_file, trace_file))

l = open(cnf_file).readline().strip()
l = l.split()

print("[4] reading trace")
f = open(trace_file)
cg_out = open(dot_file, "w+")
resolution_steps = 0

edge_count = 0

cg_out.write("digraph D {\n")
for line in f:
	if "*" not in line:
		continue
	line = line.strip().split()[:-1]
	start = line[0]
	edge_count += len(line[2:])
	resolution_steps += 1

	if edge_count > 1000:
		continue

	for end in line[2:]:
		cg_out.write("\t{} -> {}\n".format(start, end))

cg_out.write("}\n")
cg_out.close()

if edge_count <= 1000:
	os.system("dot -Tpng %s -o %s" % (dot_file, png_file))
else:
	print("graph too large skipping visualization")

print("[5] dumping stats")
print("variables: %s" % l[2])
print("clauses: %s" % l[3])
print("proof steps: %d" % resolution_steps)