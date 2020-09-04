import sys, os

try:
	full_bits = int(sys.argv[1])
except:
	full_bits = 2

picosat = "/home/yizhou7/Desktop/research/open_titan/picosat-965/picosat"

print("using %d bit width" % full_bits)

if not os.path.exists("gen"):
	os.makedirs("gen")

name = "gen/%d_bits" % full_bits
cnf_file = name + ".cnf"
trace_file = name + ".trace"
dot_file = name + ".dot"
png_file = name + ".png"

os.system("python bv_export.py %d | tail -n +4 | head -n -1 > %s" % (full_bits, cnf_file))
os.system("%s %s -t %s" % (picosat, cnf_file, trace_file))

f = open(trace_file)
content = "digraph D {\n"
for line in f:
	if "*" not in line:
		continue
	line = line.strip().split()[:-1]
	start = line[0]
	for end in line[2:]:
		content += "\t{} -> {}\n".format(start, end)
content += "}\n"

cg_out = open(dot_file, "w+")
cg_out.write(content)
cg_out.close()

os.system("dot -Tpng %s -o %s" % (dot_file, png_file))
