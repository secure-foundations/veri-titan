import sys

wmem = []

def parse_buff(lines, i, addr):
    temp = []
    addrs = []
    count = 8

    while i != len(lines):
        line = lines[i]
        if ".org" in line:
            break
        if ".word" in lines[i]:
            temp.append(lines[i][8:-1])
            addrs.append(addr)
            addr += 4
        i = i + 1
    assert len(addrs) == len(temp)
    assert len(temp) % count == 0
    temp = [temp[n:n+count] for n in range(0, len(temp), count)]
    [temp[i].reverse() for i in range(len(temp))]
    temp = ["0x" + "".join(temp[i]) for i in range(len(temp))]
    addrs = [addrs[i] for i in range(0, len(addrs), count)]
    # print("map[", end="")
    for j in range(0, len(temp)):
        wmem.append(f"{hex(addrs[j])} := {temp[j]}")
    #     if j == len(temp) - 1:
    #         print("]")
    #     else:
    #         print(",")
    return i

f = open(sys.argv[1])
lines = f.readlines()
f.close()

i = 0
addr = 0

xmem = []

while i != len(lines):
    line = lines[i]
    if ".org" in line:
        addr = int(line[4:], base=16)
        i = parse_buff(lines, i+1, addr)
    else:
        if ".word" in line:
            xmem.append(f"{addr} := 0x{line[8:-1]}")
            addr += 4
        i = i + 1
print("var xmem := map[" + ",\n".join(xmem) + "];")
print("var wmem := map[" + ",\n".join(wmem) + "];")