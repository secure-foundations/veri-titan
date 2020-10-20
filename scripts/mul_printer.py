import re

inss = ["bn.mulqacc.z          w8.0, w10.0,   0",
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

qsel = re.compile("(w[0-9]+).([0-3])")

def get_qsel(s):
    m = re.match(qsel, s)
    return m.groups(0)

def get_shift(s):
    if s == "0":
        return "0"
    if s == "64":
        return "1"
    assert False
    
so = re.compile("(w[0-9]+).(L|U)")

def get_so(s):
    m = re.match(so, s)
    w, h = m.groups(0)
    lower = "false"
    if h == "L":
        lower = "true"
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

class MulQaccAssert:
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

assertions = list()

for ins in inss:
    ins = re.split("\s+", ins)
    op = ins[0]

    if op == "bn.mulqacc.z":
        x, qx = get_qsel(ins[1])
        y, qy = get_qsel(ins[2])
        shift = get_shift(ins[3])
        print(f"BN_MULQACC_Z({x}, {qx}, {y}, {qy}, {shift});")

        c_wacc = get_fresh('wacc')

        print(f"let {c_wacc} := wacc;")
        assertions.append(MulQaccAssert("true", x, qx, y, qy, shift, c_wacc, 0))

        print("")
    elif op == "bn.mulqacc":
        x, qx = get_qsel(ins[1])
        y, qy = get_qsel(ins[2])
        shift = get_shift(ins[3])
        print(f"BN_MULQACC_SAFE({x}, {qx}, {y}, {qy}, {shift});")

        p_wacc = get_last('wacc')
        c_wacc = get_fresh('wacc')

        print(f"let {c_wacc} := wacc;")
        assertions.append(MulQaccAssert("false", x, qx, y, qy, shift, c_wacc, p_wacc))

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

        assertions.append(MulQaccAssert("false", x, qx, y, qy, shift, temp_0, p_wacc))

        assertions.append(f"assert {c_wacc} == uint256_uh({temp_0});")
        assertions.append(f"assert {temp_1} == uint256_lh({temp_0});")
        assertions.append(f"assert {c_dest} == uint256_hwb({p_dest}, {temp_1}, {l});")
        print("")

for a in assertions:
    print(a)