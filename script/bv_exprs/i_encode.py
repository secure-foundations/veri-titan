from bv_exprs import *

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

class BinOpEq:
    def __init__(self, op, dst, src1, src2):
        self.op = op
        self.dst = dst
        self.src1 = src1
        self.src2 = src2
    
    def __str__(self):
        return f"{self.dst} == {bin_ops[self.op]}_n({self.src1}, {self.src2})"

class UniOpEq:
    def __init__(self, op, dst, src):
        self.op = op
        self.dst = dst
        self.src = src

    def __str__(self):
        return f"{self.dst} == {uni_ops[self.op]}_n({self.src})"

class BaseVariab1e:
    def __init__(self, v, b):
        # n bits vector
        self.v = v
        # n + 1 bits vector
        self.ev = self.v + "'"
        # 1 bit extension
        self.b = b
    
    def __str__(self):
        return self.v

    # 1 bit extension
    def bin(self):
        return self.b

    # n + 1 bit vector
    def ext(self):
        return self.ev

    def get_defs(self):
        return [self.v, self.ev, self.b]

    # two equations:
    # ev == v + b * pow2_n
    # b * (b - 1) == 0
    def get_base_equations(self):
        return f"\t{self.ev} - {self.b} * pow2_n - {self.v},\n\t{self.b} * (1 - {self.b})"

class Constant:
    def __init__(self, v):
        self.v = v

    def bin(self):
        # FIXME: assume for now that the constant is single bit
        return "0"

    def ext(self):
        return self.v

    def __str__(self):
        return self.v

class Encoder:
    def __init__(self, q):
        self.tmp_count = 0
        self.bin_count = 0
        self.k_count = 0

        self.base_vars = dict()
        self.flat_eqs = set()
        self.polys = list()

        # flatten expressions
        (p1, p2) = self.flatten_b2(q)
        print("")

        for var in self.base_vars.values():
            self.append_poly(f"// encoding base variab1e {var}")
            self.append_poly(var.get_base_equations())

        self.encode_equations()

        self.append_poly("// encoding induction hypothesis")
        self.append_poly(f"\t{p1} - {p2}")
        self.append_poly("// encoding pow")
        self.append_poly(f"\tpow2_n_1 - 2 * pow2_n")
        self.append_poly(f"\tpow2_n_1")

        self.dump_encoding()

        print(f"ideal G = groebner(I);\nreduce({p1.ext()} - {p2.ext()}, G);")

    def append_poly(self, p):
        self.polys.append(p)

    def dump_encoding(self):
        defs = ["pow2_n", "pow2_n_1"]
        for var in self.base_vars.values():
            defs.extend(var.get_defs())
        for i in range(self.k_count):
            defs.append("k%d" % (i + 1))
        print("ring r=integer,(" + ", ".join(defs) + "),lp;")

        print("ideal I =")
        for i, poly in enumerate(self.polys):
            if i != len(self.polys) - 1:
                print(poly + ",")
            else:
                print(poly + ";")

    def flatten_b2(self, q):
        assert type(q) == z3.z3.BoolRef
        assert q.decl().name() == "="
        children = q.children()
        l = self.flatten_bvr(children[0])
        r = self.flatten_bvr(children[1])

        print("// flattened equations")
        for eq in self.flat_eqs:
            print("//\t" + str(eq))
        return (l, r)

    def flatten_bvr(self, e):
        if type(e) == z3.z3.BitVecRef:
            children = [self.flatten_bvr(child) for child in e.children()]
            num_children = len(children)
            op = str(e.decl())

            if num_children == 0:
                return self.get_fresh_base(op)

            v = self.get_fresh_tmp()

            if num_children == 1:
                eq = UniOpEq(op, v, children[0])
                self.flat_eqs.add(eq)
                return v

            if num_children == 2:
                eq = BinOpEq(op, v, children[0], children[1])
                self.flat_eqs.add(eq)
                return v

            raise Exception(f"op {op} not handled")

        elif type(e) == z3.z3.BitVecNumRef:
            return Constant(str(e))
        else:
            raise Exception(f"{type(e)} is NYI")

    def get_fresh_base(self, name):
        if name not in self.base_vars:
            b = self.get_fresh_bin()
            var = BaseVariab1e(name, b)
            self.base_vars[name] = var
        return self.base_vars[name]

    def get_fresh_tmp(self):
        self.tmp_count += 1
        t = "t%d" % self.tmp_count
        return self.get_fresh_base(t)

    def get_fresh_bin(self):
        self.bin_count += 1
        b = "b%d" % self.bin_count
        # eq = f"{b} * (1 - {b})"
        return b

    def get_fresh_k(self):
        self.k_count += 1
        t = "k%d" % self.k_count
        return t

    def encode_equations(self):
        for eq in self.flat_eqs:
            self.encode_equation(eq)

    def encode_equation(self, eq):
        if type(eq) == BinOpEq:
            self.encode_binop_equation(eq)
        elif type(eq) == UniOpEq:
            self.encode_uniop_equation(eq)
        else:
            raise Exception(f"{type(eq)} is NYI")
    
    def encode_binop_equation(self, eq):
        op = eq.op
        #  d is the destination, s1 the first source, s2 the second source
        d, s1, s2 = eq.dst, eq.src1, eq.src2
        #  get the single extension bits
        b, b1, b2 = d.bin(), s1.bin(), s2.bin()

        if op == "&":
            self.append_poly(f"// encoding {d} == and_n({s1}, {s2})")
            self.append_poly(f"\t{b} - {b1} * {b2}")
        elif op == "^":
            self.append_poly(f"// encoding {d} == xor_n({s1}, {s2})")
            self.append_poly(f"\t{b1} + {b2} - 2 * {b1} * {b2} - {b}")
        elif op == "|":
            self.append_poly(f"// encoding {d} == or_n({s1}, {s2})")
            self.append_poly(f"\t{b1} + {b2} - {b1} * {b2} - {b}")
        elif op == "+":
            self.append_poly(f"// encoding {d} == add_n({s1}, {s2})")

            # k1 is the carray from s1 + s2
            k1 = self.get_fresh_k()
            self.append_poly(f"\t{k1} * (1 - {k1})")
            self.append_poly(f"\t{d} - {s1} - {s2} + {k1} * pow2_n")

            # k2 is the carray from s1' + s2'
            k2 = self.get_fresh_k()
            self.append_poly(f"\t{k2} * (1 - {k2})")
            self.append_poly(f"\t{d.ext()} - {s1.ext()} - {s2.ext()} + {k2} * pow2_n_1")

            # self.append_poly(f"\t{b1} + {b2} + {k1} - {b} - 2 * {k2}")
        elif op == "-":
            self.append_poly(f"// encoding {d} == sub_n({s1}, {s2})")
            k1 = self.get_fresh_k()
            self.append_poly(f"\t{d} - {s1} + {s2} - {k1} * pow2_n")
            k2 = self.get_fresh_k()
            self.append_poly(f"\t{d.ext()} - {s1.ext()} + {s2.ext()} - {k2} * pow2_n_1")        
        else:
            raise Exception(f"binop {op} is NYI")
    
    def encode_uniop_equation(self, eq):
        op = eq.op
        # print(eq)
        d, s = eq.dst, eq.src
        bs, bd = s.bin(), d.bin()

        if op == "~":
            self.append_poly(f"// encoding {d} == not_n({s})")
            self.append_poly(f"\t{bs} + {bd} - 1")
            self.append_poly(f"\t{d} + {s} + 1 - pow2_n")
            self.append_poly(f"\t{d.ext()} + {s.ext()} + 1 - pow2_n_1")
        elif op == "-":
            self.append_poly(f"// encoding {d} == neg_n({s})")
            self.append_poly(f"\t{d} + {s} - pow2_n")
            self.append_poly(f"\t{d.ext()} + {s.ext()} - pow2_n_1")
        else:
            raise Exception(f"uniop {op} is NYI")

if __name__ == '__main__':
    try:
        func = sys.argv[1] + "()"
        query = eval(func)
        # prove(query)
    except:
        print("usage:\npython encode.py [query_name] [bit_number]")
        sys.exit(1)
    
    Encoder(query)
