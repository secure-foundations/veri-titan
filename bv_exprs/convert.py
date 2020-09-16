from bv_exprs import *

class Encoder:
    def __init__(self, q):
        self.tmp_count = 0
        self.bin_count = 0
        self.input_vars = dict()
        self.opaque_vars = dict()
        self.gpass = False
        self.equations = set()

        assert type(q) == z3.z3.BoolRef
        assert q.decl().name() == "="

        self.encode_br(q)
        self.gpass = True
        goal = self.encode_br(q)

        self.dump_vars() 
        print("ideal I = ")
        for eq in self.equations:
            print("\t" + eq + ",")
        print("\tpow2_n_1 - 2 * pow2_n;")

        print("ideal G = groebner(I);")
        print(f"reduce({goal}, G);")

    def encode_br(self, q):
        children = q.children()
        l = self.encode_bvr(children[0])
        r = self.encode_bvr(children[1])
        eq = l + " - " + r
        if self.gpass:
            return eq
        else:
            self.equations.add(eq)

    def encode_bvr(self, e):
        if type(e) == z3.z3.BitVecRef:
            children = [self.encode_bvr(child) for child in e.children()]
            num_children = len(children)

            if num_children == 0:
                v = str(e.decl())
                if self.gpass:
                    return v + "'"
                else:
                    self.add_input_var(v)
                    return v

            op = str(e.decl())
            var = self.get_fresh_tmp()

            if op == "&":
                self.encode_and(var, children[0], children[1])
                return var
            else:
                raise Exception("not handled")
        elif type(e) == z3.z3.BitVecNumRef:
            return str(e)
        else:
            raise Exception("not handled")

    def get_fresh_tmp(self):
        self.tmp_count += 1
        return "t%d" % self.tmp_count
    
    def get_fresh_bin(self):
        self.bin_count += 1
        b = "b%d" % self.bin_count
        eq = f"{b} * (1 - {b})"
        self.equations.add(eq)
        return b

    def add_input_var(self, v):
        if v not in self.input_vars:
            b = self.get_fresh_bin()
            self.input_vars[v] = b
            eq = f"{v}' - pow2_n_1 * {b} - {v}"
            self.equations.add(eq)

    def get_fresh_opaque(self, actual):
        if actual in self.opaque_vars:
            return self.opaque_vars[actual]
        o = "o%d" % (len(self.opaque_vars) + 1) 
        self.opaque_vars[actual] = o
        return o

    def get_assoc_bin(self, v):
        if v not in self.input_vars:
            raise Exception("not an input var")
        return self.input_vars[v]

    def encode_and(self, t, l, r):
        if self.gpass:
            o0 = self.get_fresh_opaque(f"bv_and({l}, {r}, n)")
            eq = f"{t} - {o0}"
            self.equations.add(eq)
        else:
            o0 = self.get_fresh_opaque(f"bv_and({l}, {r}, n - 1)")
            eq = f"{t} - {o0}"
            self.equations.add(eq)

            bl = self.get_assoc_bin(l)
            br = self.get_assoc_bin(r)

            b = self.get_fresh_bin()
            eq = f"{b} - {bl} * {br}"
            self.equations.add(eq)

            o1 = self.get_fresh_opaque(f"bv_and({l}', {r}', n)")
            eq = f"{o1} - pow2_n * {b} - {o0}"
            self.equations.add(eq)

    def dump_vars(self):
        vars = ["pow2_n_1", "pow2_n"]
        for v in self.input_vars:
            vars.append(f"{v}, {v}'")
        for i in range(self.bin_count):
            vars.append(f"b{i + 1}")
        for i in range(self.tmp_count):
            vars.append(f"t{i + 1}")
        for o in self.opaque_vars.values():
            vars.append(o)
        print("ring r=integer,(" + ", ".join(vars) + "),lp;")

q = bvand()
enc = Encoder(q)

# print("")
# dump_vars()