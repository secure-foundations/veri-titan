
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

INFIX=False
DAFNY=True

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

    def __eq__(self, other):
        return isinstance(other, BinBoolExpr) and \
               other.op == self.op and \
               other.src1 == self.src1 and \
               other.src2 == self.src2

    def flatten(self, varmap, carry_calc):
        return BinBoolExpr(self.op, self.src1.flatten(varmap, carry_calc), self.src2.flatten(varmap, carry_calc))

    def simp(self):
        s1 = self.src1.simp()
        s2 = self.src2.simp()

        if self.op == "&":
            if isinstance(s1, BoolConst) and s1.b:
                return s2
            if isinstance(s2, BoolConst) and s2.b:
                return s1

            if isinstance(s1, BoolConst) and not s1.b:
                return BoolConst(False)
            if isinstance(s2, BoolConst) and not s2.b:
                return BoolConst(False)
            
            if s1 == s2:
                return s1

            if isinstance(s1, UniBoolExpr) and s1.src == s2: # !s1 && s1
                return BoolConst(False)
            
            if isinstance(s2, UniBoolExpr) and s2.src == s1: # !s2 && s2
                return BoolConst(False)

        elif self.op == "|":
            if isinstance(s1, BoolConst) and s1.b:
                return BoolConst(True)
            if isinstance(s2, BoolConst) and s2.b:
                return BoolConst(True)

            if isinstance(s1, BoolConst) and not s1.b:
                return s2
            if isinstance(s2, BoolConst) and not s2.b:
                return s1
            
            if s1 == s2:
                return s1

            if isinstance(s1, UniBoolExpr) and s1.src == s2: # !s1 || s1
                return BoolConst(True)
            
            if isinstance(s2, UniBoolExpr) and s2.src == s1: # !s2 || s2
                return BoolConst(True)

        elif self.op == "^":
            if isinstance(s1, BoolConst) and s1.b:
                return UniBoolExpr('~', s2)
            if isinstance(s2, BoolConst) and s2.b:
                return UniBoolExpr('~', s1)

            if isinstance(s1, BoolConst) and not s1.b:
                return s2
            if isinstance(s2, BoolConst) and not s2.b:
                return s1
            
            if s1 == s2:
                return BoolConst(False)

            if isinstance(s1, UniBoolExpr) and s1.src == s2: # !s1 ^ s1
                return BoolConst(True)
            
            if isinstance(s2, UniBoolExpr) and s2.src == s1: # !s2 ^ s2
                return BoolConst(True)

        else:
            raise Exception("Unexpected BinBoolOp: %s" % self.op)

        return BinBoolExpr(self.op, s1, s2)

    def __str__(self):
        if INFIX:
            return f"({self.op} {self.src1} {self.src2})"
        elif DAFNY:
            if self.op == '&':
                return f"({self.src1} && {self.src2})"
            elif self.op == '|':
                return f"({self.src1} || {self.src2})"
            elif self.op == '^':
                return f"xor({self.src1}, {self.src2})"
        else:
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
        self.output = Variable(Namer.new_name("bexpr"))
        self.carry = Variable(Namer.new_name("carry")) if self.op == "+" else None

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
        if (self.op == "+"):
            s1 = self.src1.output
            s2 = self.src2.output
            return { self.carry : \
                     BinBoolExpr("|", BinBoolExpr("&", s1, s2), \
                                      BinBoolExpr("&", Variable(self.carry.name, old=True), BinBoolExpr("|", s1, s2))) }
        else:
            return {}

    def flatten(self, varmap, carry_calc):
        if self.op == "&":
            rhs = BinBoolExpr("&", self.src1.flatten(varmap, carry_calc), self.src2.flatten(varmap, carry_calc))
        elif self.op == "|":
            rhs = BinBoolExpr("|", self.src1.flatten(varmap, carry_calc), self.src2.flatten(varmap, carry_calc))
        elif self.op == "^":
            rhs = BinBoolExpr("^", self.src1.flatten(varmap, carry_calc), self.src2.flatten(varmap, carry_calc))
        elif self.op == "+":
            rhs = BinBoolExpr("^", self.src1.flatten(varmap, carry_calc), BinBoolExpr("^", self.src2.flatten(varmap, carry_calc), self.carry))
        else:
            raise Exception("Unexpected bin_op: %s" % self.op)
        return rhs

    def get_generic_bit(self):
        lhs = self.output
        if self.op == "&":
            rhs = BinBoolExpr("&", self.src1.output, self.src2.output)
        elif self.op == "|":
            rhs = BinBoolExpr("|", self.src1.output, self.src2.output)
        elif self.op == "^":
            rhs = BinBoolExpr("^", self.src1.output, self.src2.output)
        elif self.op == "+":
            rhs = BinBoolExpr("^", self.src1.output, BinBoolExpr("^", self.src2.output, self.carry))
        else:
            raise Exception("Unexpected bin_op: %s" % self.op)
        me = { lhs : rhs }
        me.update(self.src1.get_generic_bit())
        me.update(self.src2.get_generic_bit())

        me.update(self.get_generic_carry_bit())

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

    def __eq__(self, other):
        return isinstance(other, UniBoolExpr) and \
               other.op == self.op and \
               other.src == self.src

    def flatten(self, varmap, carry_calc):
        return UniBoolExpr(self.op, self.src.flatten(varmap, carry_calc))

    def simp(self):
        s = self.src.simp()
        if self.op == '~' and isinstance(s, UniBoolExpr) and s.op == '~':
            return s.src
        if self.op == '~' and isinstance(s, BoolConst):
            return BoolConst(not s.b)
        return UniBoolExpr(self.op, s)

    def __str__(self):
        if DAFNY:
            return f"(!{self.src})"
        else:
            return f"({self.op} {self.src})"

class UniOpExpr:
    def __init__(self, op, src):
        assert op in uni_ops.keys()
        self.op = op
        self.src = src
        self.bits = src.bits
        self.output = Variable(Namer.new_name("uexpr"))

    def flatten(self, varmap, carry_calc):
        return UniBoolExpr("~", self.src.flatten(varmap, carry_calc))

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
    def __init__(self, name, old=False):
        self.name = name
        self.old = old

    def __eq__(self, other):
        return isinstance(other, Variable) and \
               other.name == self.name and \
               other.old == self.old

    def __hash__(self): 
        return hash("%s" % self)

    def simp(self):
        return self

    def flatten(self, varmap, carry_calc):
        if carry_calc and "carry" in self.name and not self.old:
            return Variable(self.name, old=True)
        if self in varmap:
            return varmap[self].flatten(varmap, carry_calc)
        return self

    def __str__(self):
        if not self.old:
            return self.name
        if DAFNY:
            return f"old_{self.name}"
        else:
            return f"old({self.name})"

class InputVariable:
    names = set()

    @classmethod
    def reset(cls):
        cls.names = set()

    def __init__(self, bits, name):
        self.bits = bits
        self.name = name
        self.output = Variable(name)

        if name in self.names:
            raise Exception("Duplicate input variable name: %s" % name)
        else:
            self.names.add(name)

    def flatten(self, varmap, carry_calc):
        return Variable(self.name)

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

    def __eq__(self, other):
        return isinstance(other, BoolConst) and \
               other.b == self.b

    def simp(self):
        return self

    def flatten(self, varmap, carry_calc):
        return self

    def __str__(self):
        return "true" if self.b else "false"

class Constant:
    def __init__(self, bits, value):
        assert(value == 0 or value == 1)
        self.bits = bits
        self.value = value
        self.output = BoolConst(False)

        assert 0 <= value < 2**bits

    def flatten(self, varmap, carry_calc):
        return self.output

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


def simp_harder(e):
    prev = e
    s = prev.simp()
    while not s == prev:
        prev = s
        s = s.simp()
    return s       


def simp_test():
    es =  [BinBoolExpr('&', BoolConst(True), BoolConst(True))]
    es += [BinBoolExpr('&', BoolConst(True), BoolConst(False))]
    es += [BinBoolExpr('&', BoolConst(False), BoolConst(True))]
    es += [BinBoolExpr('&', BoolConst(False), BoolConst(False))]
    es += [BinBoolExpr('|', BoolConst(True), BoolConst(True))]
    es += [BinBoolExpr('|', BoolConst(True), BoolConst(False))]
    es += [BinBoolExpr('|', BoolConst(False), BoolConst(True))]
    es += [BinBoolExpr('|', BoolConst(False), BoolConst(False))]
    es += [BinBoolExpr('^', BoolConst(True), BoolConst(True))]
    es += [BinBoolExpr('^', BoolConst(True), BoolConst(False))]
    es += [BinBoolExpr('^', BoolConst(False), BoolConst(True))]
    es += [BinBoolExpr('^', BoolConst(False), BoolConst(False))]
    es += [BinBoolExpr('^', BinBoolExpr('&', BoolConst(True), BoolConst(True)),  BinBoolExpr('|', BoolConst(True), BoolConst(False)))]
    es += [BinBoolExpr('^', Variable("blah"), BinBoolExpr('^', BoolConst(False), Variable("foo")))]
    for e in es:
        print("Original: %s" % e)
        print("Simplified: %s" % simp_harder(e))


def real_example():
    bits = 4
#    print_formula(bits, add_commutes)
#    print_formula(bits, identity)
#    print_formula(bits, add_self2)
#    print_formula(bits, add_self4)

    #f = add_commutes(bits)
    f = identity(bits)
    print("Formula: %s" % f)
    exprs = f.get_generic_bit()
    for v, e in exprs.items():
        print(f"{v} == {e}")
        
    print("Output is: %s" % f.output)

    flat = f.flatten(exprs, False)
    print("Flattened: %s " % flat)
    print("Simplified: %s " % simp_harder(flat))

    for v, e in exprs.items():
        if "carry" in v.name:
            flat = e.flatten(exprs, True)
            flat_str = "%s" % flat
            flat_str = flat_str.replace("carry_3", "carry_1")
            flat_str = flat_str.replace("carry_5", "carry_2")
            print(f"Flattened  {v} == {flat_str}")
            simp_str = "%s" % simp_harder(flat)
            simp_str = simp_str.replace("carry_3", "carry_1")
            simp_str = simp_str.replace("carry_5", "carry_2")
            print(f"Simplified {v} == {simp_str}")
    

def main():
    #simp_test()
    real_example()

if (__name__=="__main__"):
  main()
