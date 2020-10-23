import re

mul_384 = [
    "bn.mulqacc.z          w8.0, w10.0,   0",
    "bn.mulqacc            w8.0, w10.1,  64",
    "bn.mulqacc.so w16.L,  w8.1, w10.0,  64",
    "bn.mulqacc            w8.0, w10.2,   0",
    "bn.mulqacc            w8.1, w10.1,   0",
    "bn.mulqacc            w8.2, w10.0,   0",
    "bn.mulqacc            w8.0, w10.3,  64",
    "bn.mulqacc            w8.1, w10.2,  64",
    "bn.mulqacc            w8.2, w10.1,  64",
    "bn.mulqacc.so w16.U,  w8.3, w10.0,  64",
    "bn.mulqacc            w8.0, w11.0,   0",
    "bn.mulqacc            w8.1, w10.3,   0",
    "bn.mulqacc            w8.2, w10.2,   0",
    "bn.mulqacc            w8.3, w10.1,   0",
    "bn.mulqacc            w9.0, w10.0,   0",
    "bn.mulqacc            w8.0, w11.1,  64",
    "bn.mulqacc            w8.1, w11.0,  64",
    "bn.mulqacc            w8.2, w10.3,  64",
    "bn.mulqacc            w8.3, w10.2,  64",
    "bn.mulqacc            w9.0, w10.1,  64",
    "bn.mulqacc.so w17.L,  w9.1, w10.0,  64",
    "bn.mulqacc            w8.1, w11.1,   0",
    "bn.mulqacc            w8.2, w11.0,   0",
    "bn.mulqacc            w8.3, w10.3,   0",
    "bn.mulqacc            w9.0, w10.2,   0",
    "bn.mulqacc            w9.1, w10.1,   0",
    "bn.mulqacc            w8.2, w11.1,  64",
    "bn.mulqacc            w8.3, w11.0,  64",
    "bn.mulqacc            w9.0, w10.3,  64",
    "bn.mulqacc.so w17.U,  w9.1, w10.2,  64",
    "bn.mulqacc            w8.3, w11.1,   0",
    "bn.mulqacc            w9.0, w11.0,   0",
    "bn.mulqacc            w9.1, w10.3,   0",
    "bn.mulqacc            w9.0, w11.1,  64",
    "bn.mulqacc.so w18.L,  w9.1, w11.0,  64",
    "bn.mulqacc.so w18.U,  w9.1, w11.1,   0"]

mul_256_half = [
    "bn.mulqacc.z          w28.0, w29.0,  0",
    "bn.mulqacc            w28.1, w29.0, 64",
    "bn.mulqacc.so   w1.L, w28.0, w29.1, 64",
    "bn.mulqacc            w28.2, w29.0,  0",
    "bn.mulqacc            w28.1, w29.1,  0",
    "bn.mulqacc            w28.0, w29.2,  0",
    "bn.mulqacc            w28.3, w29.0, 64",
    "bn.mulqacc            w28.2, w29.1, 64",
    "bn.mulqacc            w28.1, w29.2, 64",
    "bn.mulqacc.so   w1.U, w28.0, w29.3, 64",]

mul_256 = [
    "bn.mulqacc.z        w28.0, w29.0, 0",
    "bn.mulqacc          w28.1, w29.0, 64",
    "bn.mulqacc.so w2.L, w28.0, w29.1, 64",
    "bn.mulqacc          w28.2, w29.0, 0",
    "bn.mulqacc          w28.1, w29.1, 0",
    "bn.mulqacc          w28.0, w29.2, 0",
    "bn.mulqacc          w28.3, w29.0, 64",
    "bn.mulqacc          w28.2, w29.1, 64",
    "bn.mulqacc          w28.1, w29.2, 64",
    "bn.mulqacc.so w2.U, w28.0, w29.3, 64",
    "bn.mulqacc          w28.3, w29.1, 0",
    "bn.mulqacc          w28.2, w29.2, 0",
    "bn.mulqacc          w28.1, w29.3, 0",
    "bn.mulqacc          w28.3, w29.2, 64",
    "bn.mulqacc.so w3.L, w28.2, w29.3, 64",
    "bn.mulqacc.so w3.U, w28.3, w29.3, 0",]

qsel = re.compile("(w[0-9]+).([0-3])")
so = re.compile("(w[0-9]+).(L|U)")

inputs = set()

def get_qsel(s):
    m = re.match(qsel, s)
    inputs.add(m.group(1))
    return m.groups(0)

def get_shift(s):
    if s == "0":
        return 0
    if s == "64":
        return 1
    assert False
    
def get_so(s):
    m = re.match(so, s)
    w, h = m.groups(0)
    lower = "false"
    if h == "L":
        lower = "true"
    else:
        assert h == "U"
    return (w, lower)

ghost_count = dict()

def get_fresh(var):
    if var not in ghost_count:
        ghost_count[var] = 0
    else:
        ghost_count[var] += 1
    return f"{var}_g{ghost_count[var]}"

def get_last(var):
    if var not in ghost_count:
        return None
    return f"{var}_g{ghost_count[var]}"

map_128 = dict()

map_256 = dict()

def lookup_128(name):
    return map_128[name]

def lookup_256(name):
    if name not in map_256:
        assert name.endswith("_g0")
        l = [name + f"_{i}" for i in range(4)]
        l.reverse()
        return l
    return map_256[name]

def quarter_expansion(f, qs):
    return (f"{f} - {qs[0]} * B^3 - {qs[1]} * B^2 - {qs[2]} * B - {qs[3]}")

def stand_quarter_expansion(f):
    return (f"{f} - {f}_3 * B^3 - {f}_2 * B^2 - {f}_1 * B - {f}_0")

class MulQaccCons:
    def __init__(self, zero, x, qx, y, qy, shift, n_wacc, o_wacc):
        assert isinstance(zero, bool)
        self.zero = zero
        self.x = x
        self.qx = qx
        self.y = y
        self.qy = qy
        self.shift = shift
        self.o_wacc = o_wacc
        self.n_wacc = n_wacc

    def __str__(self):
        zero = "true" if self.zero else "false"
        return f"assert {self.n_wacc} == bn_mulqacc_safe({zero}, {self.x}, {self.qx}, {self.y}, {self.qy}, {self.shift}, {self.o_wacc});"

    def print_eq(self):
        product = f"{self.x}_{self.qx} * {self.y}_{self.qy}"
        if self.shift == 0:
            shift = product
        else:
            assert self.shift == 1
            shift = product + " * B"

        if self.zero:
            return [f"{self.n_wacc} - {shift}"]
        else:
            return [f"{self.n_wacc} - {shift} - {self.o_wacc}"]

class HalfCons:
    def __init__(self, src, ldst, hdst):
        self.src = src
        self.ldst = ldst
        self.hdst = hdst
    
    def __str__(self):
        return f"assert {self.ldst} == uint256_lh({self.src});\nassert {self.hdst} == uint256_uh({self.src});"

    def print_eq(self):
        s = self.src
        map_128[self.ldst] = [f"{s}_1", f"{s}_0"]
        return [stand_quarter_expansion(s), f"{self.hdst} - {s}_3 * B - {s}_2"]

class WriteBackCons:
    def __init__(self, lower, n_dest, o_dest, src):
        assert lower in {"true", "false"}
        self.lower = True if lower == "true" else False
        self.n_dest = n_dest
        self.o_dest = o_dest
        self.src = src

    def __str__(self):
        l = "true" if self.lower else "false"
        return f"assert {self.n_dest} == uint256_hwb({self.o_dest}, {self.src}, {l});"

    def print_eq(self):
        src_exp = lookup_128(self.src)
        # print(src_exp)
        old_exp = lookup_256(self.o_dest)
        # print(old_exp)
        if self.lower:
            new_exp = old_exp[:2] + src_exp
        else:
            new_exp = src_exp + old_exp[2:]

        map_256[self.n_dest] = new_exp
        return [quarter_expansion(self.n_dest, new_exp)]

assertions = list()

import sys

target = eval(sys.argv[1])

for ins in target:
    ins = re.split("\s+", ins)
    op = ins[0]

    if op == "bn.mulqacc.z":
        x, qx = get_qsel(ins[1])
        y, qy = get_qsel(ins[2])
        shift = get_shift(ins[3])
        print(f"BN_MULQACC_Z({x}, {qx}, {y}, {qy}, {shift});")

        c_wacc = get_fresh('wacc')

        print(f"let {c_wacc} := wacc;")
        assertions.append(MulQaccCons(True, x, qx, y, qy, shift, c_wacc, 0))

        print("")
    elif op == "bn.mulqacc":
        x, qx = get_qsel(ins[1])
        y, qy = get_qsel(ins[2])
        shift = get_shift(ins[3])
        print(f"BN_MULQACC_SAFE({x}, {qx}, {y}, {qy}, {shift});")

        p_wacc = get_last('wacc')
        c_wacc = get_fresh('wacc')

        print(f"let {c_wacc} := wacc;")
        assertions.append(MulQaccCons(False, x, qx, y, qy, shift, c_wacc, p_wacc))

        print("")
    else:
        assert op == "bn.mulqacc.so"
        d, l = get_so(ins[1])

        x, qx = get_qsel(ins[2])
        y, qy = get_qsel(ins[3])
        shift = get_shift(ins[4])

        p_dest = get_last(d)
        if p_dest is None:
            p_dest = get_fresh(d)
            print(f"let {p_dest} := {d};")

        print(f"BN_MULQACC_SO_SAFE({d}, {l}, {x}, {qx}, {y}, {qy}, {shift});")

        c_dest = get_fresh(d)
        p_wacc = get_last('wacc');
        c_wacc = get_fresh('wacc')

        temp_0 = get_fresh('temp')
        temp_1 = get_fresh('temp')

        print(f"let {c_dest} := {d};")
        print(f"let {temp_0} := bn_mulqacc_safe(false, {x}, {qx}, {y}, {qy}, {shift}, {p_wacc});")
        print(f"let {temp_1} := uint256_lh({temp_0});")

        print(f"let {c_wacc} := wacc;")

        assertions.append(MulQaccCons(False, x, qx, y, qy, shift, temp_0, p_wacc))
        assertions.append(HalfCons(temp_0, temp_1, c_wacc))
        assertions.append(WriteBackCons(l, c_dest, p_dest, temp_1))
        print("")

for a in assertions:
    print(a)

print("")

eqs = [stand_quarter_expansion(input) for input in inputs]
for a in assertions:
    # print(a)
    # for i in a.print_eq():
    #     print(i)
    # print("")
    eqs += a.print_eq()
eqs = ",\n".join(eqs)

l = re.split(",\n|\s", eqs)
l = [i for i in l if i not  in {"-", "*", "", "B^2", "B^3"}]
l = list(set(l))

print("ring r=integer,(" + ",".join(l) + "),lp;")
print("ideal I = " + eqs + ";")