
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
        self.op = op
        self.src1 = src1
        self.src2 = src2
        assert src1.bits == src2.bits
        self.bits = src1.bits
    
    def __str__(self):
        return f"({self.src1} {bin_ops[self.op]} {self.src2})"

class UniOpExpr:
    def __init__(self, op, src):
        self.op = op
        self.src = src
        self.bits = src.bits

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


    def __str__(self):
        return self.name

class Constant:
    def __init__(self, bits, value):
        self.bits = bits
        self.value = value

        assert 0 <= value < 2**bits


def add_commutes(bits):
    x = InputVariable(bits, "x")
    y = InputVariable(bits, "y")
    return BinOpExpr("-", BinOpExpr("+", x, y), BinOpExpr("+", y, x))


def add_self4(bits):
    x = InputVariable(bits, "x")
    return BinOpExpr("+", BinOpExpr("+", x, x), BinOpExpr("+", x, x))

def main():
    print(add_commutes(4))
    print(add_self4(4))

if (__name__=="__main__"):
  main()
