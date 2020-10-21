import re

inss_384 = ["bn.mulqacc.z          w8.0, w10.0,   0",
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

inss_mulh = [
    "bn.mulqacc.z      w28.0, w29.0, 0",
    "bn.mulqacc        w28.1, w29.0, 64",
    "bn.mulqacc        w28.0, w29.1, 64",
    "bn.mulqacc        w28.1, w29.1, 128",]

qsel = re.compile("(w[0-9]+).([0-3])")

def get_qsel(s):
    m = re.match(qsel, s)
    return m.groups(0)

def get_shift(s):
    if s == "0":
        return 0
    if s == "64":
        return 1
    if s == "128":
        return 2
    raise Exception("unhandled")
    
so = re.compile("(w[0-9]+).(L|U)")

def get_so(s):
    m = re.match(so, s)
    w, h = m.groups(0)
    lower = False
    if h == "L":
        lower = True
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

class MulQaccCons:
    def __init__(self, zero, x, qx, y, qy, shift, n_wacc, o_wacc):
        self.zero = zero
        self.x = x
        self.qx = qx
        self.y = y
        self.qy = qy
        self.shift = shift
        self.o_wacc = o_wacc
        self.n_wacc = n_wacc

    def __str__(self):
        return f"assert {self.n_wacc} == bn_mulqacc_safe({self.zero}, {self.x}, {self.qx}, {self.y}, {self.qy}, {self.shift}, {self.o_wacc});"

    def get_equations(self):
        product = f"{self.x}_{self.qx} * {self.y}_{self.qy}"

        if self.shift == 0:
            shift = product
        elif self.shift == 1:
            shift = product + " * B"
        elif self.shift == 2:
            shift = product + " * B * B"
        else:
            raise Exception("unhandled")

        if self.zero == "true":
            print(f"{self.n_wacc} - {shift}")
        else:
            print(f"{self.n_wacc} - {shift} - {self.o_wacc}")

class HalfCons:
    def __init__(self, lower, src, dst):
        self.lower = lower
        self.src = src
        self.dst= dst
    
    def __str__(self):
        if self.lower:
            return f"assert {self.dst} == uint256_lh({self.src});"
        return f"assert {self.dst} == uint256_uh({self.src});"

    def get_equations(self):
        if self.lower:
            print(f"{self.dst} - {self.src}_1 * B - {self.src}_0")
        else:
            print(f"{self.dst} - {self.src}_3 * B - {self.src}_2")

class WriteBackCons:
    def __init__(self, lower, n_dest, o_dest, src):
        self.lower = lower
        self.n_dest = n_dest
        self.o_dest = o_dest
        self.src = src

    def __str__(self):
        if self.lower:
            lower = "true"
        else:
            lower = "false"
        return f"assert {self.n_dest} == uint256_hwb({self.o_dest}, {self.src}, {lower}"

    def get_equations(self):
        if self.lower:
            print(f"{self.n_dest} - {self.o_dest}_3 * B^3 - {self.o_dest}_2 * B^2 - {self.src}_1 * B - {self.src}_0")
        else:
            print(f"{self.n_dest} - {self.src}_1 * B^3 - {self.src}_0 * B^2 - {self.o_dest}_1 * B - {self.o_dest}_0")

assertions = list()

for ins in inss_384:
    ins = re.split("\s+", ins)
    op = ins[0]

    if op == "bn.mulqacc.z":
        x, qx = get_qsel(ins[1])
        y, qy = get_qsel(ins[2])
        shift = get_shift(ins[3])
        print(f"BN_MULQACC_Z({x}, {qx}, {y}, {qy}, {shift});")

        c_wacc = get_fresh('wacc')

        print(f"let {c_wacc} := wacc;")
        assertions.append(MulQaccCons("true", x, qx, y, qy, shift, c_wacc, 0))

        print("")
    elif op == "bn.mulqacc":
        x, qx = get_qsel(ins[1])
        y, qy = get_qsel(ins[2])
        shift = get_shift(ins[3])
        print(f"BN_MULQACC_SAFE({x}, {qx}, {y}, {qy}, {shift});")

        p_wacc = get_last('wacc')
        c_wacc = get_fresh('wacc')

        print(f"let {c_wacc} := wacc;")
        assertions.append(MulQaccCons("false", x, qx, y, qy, shift, c_wacc, p_wacc))

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

        assertions.append(MulQaccCons("false", x, qx, y, qy, shift, temp_0, p_wacc))

        assertions.append(HalfCons(False, temp_0, c_wacc))
        assertions.append(HalfCons(True, temp_0, temp_1))
        assertions.append(WriteBackCons(l, c_dest, p_dest, temp_1))

        print("")

for a in assertions:
    print(a)

for a in assertions:
    a.get_equations()