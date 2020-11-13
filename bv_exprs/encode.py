
bin_ops = {
    "&" : "and",
    "|" : "or",
    "^" : "xor",
    "+" : "add",
    "-" : "sub",
}

uni_ops = {
    "-" : "neg",
    "~" : "not",
}

class Namer:
    count = 0

    @classmethod
    def new_name(cls, s):
        cls.count = cls.count + 1
        return f"{s}_{cls.count}"

    @classmethod
    def reset(cls):
        cls.count = 0

class BinBoolExpr:
    def __init__(self, op, src1, src2):
        assert op == "&" or op == "|" or op == "^"
        self.op = op
        self.src1 = src1
        self.src2 = src2

    def __str__(self):
        return f"({self.src1} {self.op} {self.src2})"

class BinOpExpr:
    def __init__(self, op, src1, src2):
        assert src1.bits == src2.bits
        assert op in bin_ops.keys()
        if op == "-":
            op = "+"
            src2 = BinOpExpr("+", UniOpExpr("~", src2), Constant(src1.bits, 1))
        self.op = op
        self.src1 = src1
        self.src2 = src2
        self.bits = src1.bits
        self.output = Namer.new_name("bexpr")
        self.carry = Namer.new_name("carry") if self.op == "+" else None

    def get_carry_bit(self, i):
        assert 0 <= i < self.bits
        if i == 0:
            s1 = self.src1.get_bit(i)
            s2 = self.src2.get_bit(i)
            return "(%s & %s)" % (s1, s2)
        else:
            s1 = self.src1.get_bit(i)
            s2 = self.src2.get_bit(i)
            return "(((%s) & (%s)) | ((%s) & ((%s) | (%s))))" % (s1, s2, self.get_carry_bit(i-1), s1, s2)

    def get_generic_carry_bit(self):
        assert (self.op == "+")
        s1 = self.src1.output
        s2 = self.src2.output
        return  s1 + " & " + s2 + " | (" + self.carry + " & (" + s1 + " | " + s2 + "))"

    def get_generic_bit(self):
        lhs = self.output
        if self.op == "&":
            rhs = BinBoolExpr("&", self.src1.output, self.src2.output)
        elif self.op == "^":
            rhs = BinBoolExpr("^", self.src1.output, self.src2.output)
        elif self.op == "+":
            rhs = BinBoolExpr("^", self.src1.output, BinBoolExpr("^", self.src2.output, self.carry))
        else:
            raise Exception("Unexpected bin_op: %s" % self.op)
        me = { lhs : rhs }
        me.update(self.src1.get_generic_bit())
        me.update(self.src2.get_generic_bit())
        return me

    def get_bit(self, i):
        assert 0 <= i < self.bits
        if self.op == "&":
            return self.src1.get_bit(i) + " & " + self.src2.get_bit(i)
        elif self.op == "^":
            return self.src1.get_bit(i) + " ^ " + self.src2.get_bit(i)
        elif self.op == "+":
            if i == 0:
                return "(" + self.src1.get_bit(i) + ") ^ (" + self.src2.get_bit(i) + ")"
            else:
                return self.src1.get_bit(i) + " ^ " + self.src2.get_bit(i) + \
                        " ^ carry(%s[%d], %s[%d])" % (self.src1, i-1, self.src2, i-1) 
                #return self.src1.get_bit(i) + " ^ " + self.src2.get_bit(i) + f" ^ carry(%s, %s)" % (self.src1.get_bit(i-1), self.src2.get_bit(i-1)) 
                #return "(" + self.src1.get_bit(i) + ") ^ (" + self.src2.get_bit(i) + ") ^ (" + self.get_carry_bit(i-1) + ")"
        elif self.op == "-":
            raise Exception("Subtraction should have been converted during construction")
        else:
            raise Exception("Unexpected bin_op: %s" % self.op)

    
    def __str__(self):
        return f"({self.src1} {bin_ops[self.op]} {self.src2})"

class UniBoolExpr:
    def __init__(self, op, src):
        assert op in uni_ops.keys()
        self.op = op
        self.src = src

    def __str__(self):
        return f"({self.op} {self.src})"

class UniOpExpr:
    def __init__(self, op, src):
        assert op in uni_ops.keys()
        self.op = op
        self.src = src
        self.bits = src.bits
        self.output = Namer.new_name("uexpr")

    def get_generic_bit(self):
        lhs = self.output
        if self.op == "-":
            raise Exception("Negation is not yet supported")
        elif self.op == "~":
            rhs = UniBoolExpr("~", self.src.output)
        else:
            raise Exception("Unexpected uni_op: %s" % self.op)
        me = { lhs : rhs }
        me.update(self.src.get_generic_bit())
        return me

    def get_bit(self, i):
        assert 0 <= i < self.bits
        if self.op == "-":
            raise Exception("Negation is not yet supported")
        elif self.op == "~":
            return "!(" + self.src.get_bit(i) + ")"
        else:
            raise Exception("Unexpected uni_op: %s" % self.op)

    def __str__(self):
        return f"({uni_ops[self.op]} {self.src})"

class Variable:
    def __init__(self, name):
        self.name = name
        #self.output = name

    def __str__(self):
        return self.name

class InputVariable:
    names = set()

    @classmethod
    def reset(cls):
        cls.names = set()

    def __init__(self, bits, name):
        self.bits = bits
        self.name = name
        self.output = name

        if name in self.names:
            raise Exception("Duplicate input variable name: %s" % name)
        else:
            self.names.add(name)

    def get_generic_bit(self):
        #return { self.name : Variable(self.name) }
        return {}

    def get_bit(self, i):
        assert 0 <= i < self.bits
        return f"{self.name}[{i}]"

    def __str__(self):
        return self.name

class BoolConst:
    def __init__(self, b):
        self.b = b

    def __str__(self):
        return "True" if self.b else "False"

class Constant:
    def __init__(self, bits, value):
        assert(value == 0 or value == 1)
        self.bits = bits
        self.value = value
        self.output = BoolConst(False)

        assert 0 <= value < 2**bits

    def get_generic_bit(self):
        return {}

    def get_bit(self, i):
        assert 0 <= i < self.bits
        return "%d" % ((self.value / 2**i) % 2)

    def __str__(self):
        return "%d" % self.value


# Clear out formula state
def reset():
    InputVariable.reset()
    Namer.reset()

def identity(bits):
    x = InputVariable(bits, "x")
    return BinOpExpr("-", x, x)


def add_commutes(bits):
    x = InputVariable(bits, "x")
    y = InputVariable(bits, "y")
    return BinOpExpr("-", BinOpExpr("+", x, y), BinOpExpr("+", y, x))

def add_self2(bits):
    x = InputVariable(bits, "x")
    return BinOpExpr("+", x, x)

def add_self4(bits):
    x = InputVariable(bits, "x")
    return BinOpExpr("+", BinOpExpr("+", x, x), BinOpExpr("+", x, x))

def print_formula(bits, form):
    f = form(bits)
    print("Formula: %s" % f)
    for i in range(bits):
        print("  Bit[%d] == %s" % (i, f.get_bit(i)))
    print()
    reset()


def main():
    bits = 4
#    print_formula(bits, add_commutes)
#    print_formula(bits, identity)
#    print_formula(bits, add_self2)
#    print_formula(bits, add_self4)
    f = add_commutes(bits)
    print("Formula: %s" % f)
    exprs = f.get_generic_bit()
    for v, e in exprs.items():
        print(f"{v} == {e}")
        
    print("Output is: " + f.output)

if (__name__=="__main__"):
  main()
