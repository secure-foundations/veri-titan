from bv_exprs import *

class BinOpEq:
    def __init__(self, op, dst, src1, src2):
        self.op = op
        self.dst = dst
        self.src1 = src1
        self.src2 = src2
    
    def __str__(self):
        if self.op == "&":
            return f"{self.dst} = {self.src1} & {self.src2}"
        raise Exception("NYI")

    # def encode():
    #     print("bv_and(x', y', n) == pow2(n) * bv_and(b0, b1, 1) + bv_and(x, y, n - 1)")

class UniOpEq:
    def __init__(self, op, dst, src):
        self.op = op
        self.dst = dst
        self.src = src

    def __str__(self):
        if self.op == "":
            return f"{self.dst} = {self.src}"
        raise Exception("NYI")

class BaseVariable:
    def __init__(self, v, b):
        self.v = v
        self.ev = v + "'"
        self.b = b
    
    def get_base(self):
        return self.v

    def get_ext_bin(self):
        return self.b
    
    def get_defs(self):
        return [self.v, self.ev, self.b]

    def get_base_equations(self):
        return f"\t{self.ev} - {self.b} * pow2_n - {self.v},\n\t{self.b} * (1 - {self.b})," 

class Encoder:
    def __init__(self, q):
        self.tmp_count = 0
        self.bin_count = 0
        self.base_vars = set()
        self.equations = set()

        # flatten expressions
        self.flatten_br(q)

        base_vars = self.base_vars
        self.base_vars = dict()

        # create base variables
        defs = []
        for v in base_vars:
            b = self.get_fresh_bin()
            var = BaseVariable(v, b)
            self.base_vars[v] = var
            defs.extend(var.get_defs())
            print(var.get_base_equations())

        print("ring r=integer,(" + ", ".join(defs) + "),lp;")
        print("// done encoding base vars\n")

        self.encode_equations()

    def flatten_br(self, q):
        assert type(q) == z3.z3.BoolRef
        assert q.decl().name() == "="
        children = q.children()
        l = self.flatten_bvr(children[0])
        r = self.flatten_bvr(children[1])
        # print("IH:")
        print(UniOpEq("", l, r))

    def flatten_bvr(self, e):
        if type(e) == z3.z3.BitVecRef:
            children = [self.flatten_bvr(child) for child in e.children()]
            num_children = len(children)

            if num_children == 0:
                var = str(e.decl())
                self.base_vars.add(var)
                return var

            op = str(e.decl())
            v = self.get_fresh_tmp()

            if op == "&":
                [l, r] = children
                eq = BinOpEq(op, v, l, r)
                self.equations.add(eq)
                # print(eq)
                return v
            else:
                raise Exception(f"op {op} not handled")
        elif type(e) == z3.z3.BitVecNumRef:
            return str(e)
        raise Exception("not handled")

    def get_fresh_tmp(self):
        self.tmp_count += 1
        t = "t%d" % self.tmp_count
        self.base_vars.add(t)
        return t

    def get_fresh_bin(self):
        self.bin_count += 1
        b = "b%d" % self.bin_count
        # eq = f"{b} * (1 - {b})"
        return b

    def get_ext_bin(self, var):
        if var not in self.base_vars:
            raise Exception("not a base var")
        return self.base_vars[var].get_ext_bin()

    def encode_equations(self):
        for eq in self.equations:
            self.encode_equation(eq)

    def encode_equation(self, eq):
        if eq.op == "&":
            d, s1, s2 = eq.dst, eq.src1, eq.src2
            print(f"// [original] {d} == and_n({s1}, {s2})")
            bl = self.get_ext_bin(s1)
            br = self.get_ext_bin(s2)
            b = self.get_ext_bin(d)
            # print(f"\t{d}' - pow2_n * {b} - {d},")
            eq = f"\t{b} - {bl} * {br},"
            print(eq)
            # print("")
        else:
            raise Exception("NYI")

    # def encode_bvr(self, e):
    #     if type(e) == z3.z3.BitVecRef:
    #         children = [self.encode_bvr(child) for child in e.children()]
    #         num_children = len(children)

    #         if num_children == 0:
    #             v = str(e.decl())
    #             if self.gpass:
    #                 return v + "'"
    #             else:
    #                 self.add_input_var(v)
    #                 return v
    #         op = str(e.decl())
    #         var = self.get_fresh_tmp()

    #         if op == "&":
    #             self.encode_and(var, children[0], children[1])
    #             return var
    #         if op == "^":
    #             self.encode_xor(var, children[0], children[1])
    #             return var
    #         else:
    #             raise Exception(f"op {op} not handled")
    #     elif type(e) == z3.z3.BitVecNumRef:
    #         return str(e)
    #     else:
    #         raise Exception("not handled")

    # def encode_xor(self, t, l, r):
    #     if self.gpass:
    #         o0 = self.get_opaque(f"bv_xor({l}, {r}, n)")
    #         eq = f"{t} - {o0}"
    #         self.equations.add(eq)
    #     else:
    #         # -b + bl + br - 2 * bl * br == 0
    #         o0 = self.get_opaque(f"bv_xor({l}, {r}, n - 1)")
    #         eq = f"{t} - {o0}"
    #         self.equations.add(eq)

    #         bl = self.get_assoc_bin(l)
    #         br = self.get_assoc_bin(r)
    #         b = self.get_fresh_bin()
    #         eq = f"{bl} + {br} - 2 * {bl} * {br} - {b}"
    #         self.equations.add(eq)

    #         o1 = self.get_opaque(f"bv_xor({l}', {r}', n)")
    #         eq = f"{o1} - pow2_n * {b} - {o0}"
    #         self.equations.add(eq)

    # def get_opaque(self, actual):
    #     if actual in self.opaque_vars:
    #         return self.opaque_vars[actual]
    #     o = "o%d" % (len(self.opaque_vars) + 1) 
    #     # print(f"[DEBUG] allocating {o} = {actual}")
    #     self.opaque_vars[actual] = o
    #     return o

    # def get_assoc_bin(self, v):
    #     if v not in self.base_vars:
    #         raise Exception("not an nbits var")
    #     return self.base_vars[v]

    # def dump_vars(self):
    #     vars = ["pow2_n_1", "pow2_n"]
    #     for v in self.base_vars:
    #         vars.append(f"{v}, {v}'")
    #     for i in range(self.bin_count):
    #         vars.append(f"b{i + 1}")
    #     for o in self.opaque_vars.values():
    #         vars.append(o)
    #     print("ring r=integer,(" + ", ".join(vars) + "),lp;")

q = bvand_nested()
enc = Encoder(q)

# print("")
# dump_vars()