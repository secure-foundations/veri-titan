
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

    def get_carry_bit(self, i):
        assert 0 <= i < self.bits
        s1 = self.src1.get_bit(0)
        s2 = self.src2.get_bit(0)
        if i == 0:
            return "(%s & %s)" % (s1, s2)
        else:
            return "(((%s) & (%s)) | ((%s) & ((%s) ^ (%s))))" % (s1, s2, self.get_carry_bit(i-1), s1, s2)

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
                #return self.src1.get_bit(i) + " ^ " + self.src2.get_bit(i) + f" ^ carry(%s, %s)" % (self.src1.get_bit(i-1), self.src2.get_bit(i-1)) 
                return "(" + self.src1.get_bit(i) + ") ^ (" + self.src2.get_bit(i) + ") ^ (" + self.get_carry_bit(i-1) + ")"
        elif self.op == "-":
            raise Exception("Subtraction is not yet supported")
        else:
            raise Exception("Unexpected bin_op: %s" % self.op)

    
    def __str__(self):
        return f"({self.src1} {bin_ops[self.op]} {self.src2})"

class UniOpExpr:
    def __init__(self, op, src):
        assert op in uni_ops.keys()
        self.op = op
        self.src = src
        self.bits = src.bits

    def get_bit(self, i):
        assert 0 <= i < self.bits
        if self.op == "-":
            raise Exception("Negation is not yet supported")
        elif self.op == "~":
            return "!(" + self.src.get_bit(i) + ")"
        else:
            raise Exception("Unexpected uni_op: %s" % self.op)

    def __str__(self):
        return f"({uni_ops[self.op]}{self.src})"

class InputVariable:
    names = set()

    def __init__(self, bits, name):
        self.bits = bits
        self.name = name

#        if name in self.names:
#            raise Exception("Duplicate input variable name: %s" % name)
#        else:
#            self.names.add(name)

    def get_bit(self, i):
        assert 0 <= i < self.bits
        return f"{self.name}[{i}]"

    def __str__(self):
        return self.name

class Constant:
    def __init__(self, bits, value):
        self.bits = bits
        self.value = value

        assert 0 <= value < 2**bits

    def get_bit(self, i):
        assert 0 <= i < self.bits
        return "%d" % ((self.value / 2**i) % 2)

    def __str__(self):
        return "%d" % self.value

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

def main():
    print("Formula: %s" % add_commutes(4))
    print("  Bit[0] == %s" % add_commutes(4).get_bit(0))
    print("  Bit[1] == %s" % add_commutes(4).get_bit(1))
    print("  Bit[2] == %s" % add_commutes(4).get_bit(2))

    print("Formula: %s" % add_self2(4))
    print("  Bit[0] == %s" % add_self2(4).get_bit(0))
    print("  Bit[1] == %s" % add_self2(4).get_bit(1))
    print("  Bit[2] == %s" % add_self2(4).get_bit(2))

    print("Formula: %s" % add_self4(4))
    print("  Bit[0] == %s" % add_self4(4).get_bit(0))
    print("  Bit[1] == %s" % add_self4(4).get_bit(1))
    print("  Bit[2] == %s" % add_self4(4).get_bit(2))

if (__name__=="__main__"):
  main()
