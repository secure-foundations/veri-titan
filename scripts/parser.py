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
so = re.compile("(w[0-9]+).(L|U)")

def get_qsel(s):
    m = re.match(qsel, s)
    return m.groups(0)

def get_shift(s):
    if s == "0":
        return "0"
    if s == "64":
        return "1"
    assert False

def get_so(s):
    m = re.match(so, s)
    w, h = m.groups(0)
    lower = False
    if h == "L":
        lower = True
    return (w, lower)

class MulQuacc:
    def __init__(self, zero, x, qx, y, qy, shift):
        self.zero = zero
        self.x = x
        self.qx = qx
        self.y = y
        self.qy = qy
        self.shift = shift

    def __str__(self):
        if self.zero:
            return f"BN_MULQACC_Z({self.x}, {self.qx}, {self.y}, {self.qy}, {self.shift});"
        else:
            return f"BN_MULQACC_SAFE({self.x}, {self.qx}, {self.y}, {self.qy}, {self.shift});"

class MulQuaccSo(MulQuacc):
    def __init__(self, d, lower, zero, x, qx, y, qy, shift):
        MulQuacc.__init__(self, zero, x, qx, y, qy, shift)
        self.d = d
        self.lower = lower

    def __str__(self):
        l = "true" if self.lower else "false" 
        return f"BN_MULQACC_SO_SAFE({self.d}, {l}, {self.x}, {self.qx}, {self.y}, {self.qy}, {self.shift});"

class Parser:
    def __init__(self, inss):
        self.ghost_count = dict()
        for ins in inss:
            self.parse_ins(ins)
        
    def parse_ins(self, ins):
        ins = re.split("\s+", ins)
        op = ins[0]
        
        if op in {"bn.mulqacc.z", "bn.mulqacc"}:
            zero = op == "bn.mulqacc.z"
            x, qx = get_qsel(ins[1])
            y, qy = get_qsel(ins[2])
            shift = get_shift(ins[3])

            ins = MulQuacc(zero, x, qx, y, qy, shift)
            print(ins)
        else:
            assert op == "bn.mulqacc.so"
            d, l = get_so(ins[1])
            x, qx = get_qsel(ins[2])
            y, qy = get_qsel(ins[3])
            shift = get_shift(ins[4])

            ins = MulQuaccSo(d, l, False, x, qx, y, qy, shift)
            print(ins)

p = Parser(inss)