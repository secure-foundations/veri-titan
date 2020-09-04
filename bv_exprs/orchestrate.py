import sys, os

try:
	full_bits = int(sys.argv[1])
except:
	full_bits = 2

print("using %d bit width" % full_bits)

# /home/yizhou7/Desktop/research/open_titan/picosat-965/picosat
os.system("python bv_export.py %d | tail -n +4 | head -n -1", % full_bits)

# f = open(sys.argv[1])
# content = "digraph D {\n"
# for line in f:
# 	if "*" not in line:
# 		continue
# 	line = line.strip().split()[:-1]
# 	start = line[0]
# 	for end in line[2:]:
# 		content += "\t{} -> {}\n".format(start, end)
# content += "}\n"

# print(content)