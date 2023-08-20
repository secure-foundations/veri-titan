import random

B = "B"
B2 = "B^2"
B3 = "B^3"
B4 = "B^4"

class FullWord:
    def __init__(self, name):
        self.name = name
    
    def full(self):
        return self.name

    def quater(self, i):
        assert i in {0, 1, 2, 3}
        return f"{self.name}_q{i}"

    def half(self, i):
        assert i in {0, 1}
        return f"{self.name}_h{i}"

    def get_equations(self):
        f = self.full()

        h0 = self.half(0)
        h1 = self.half(1)

        q0 = self.quater(0)
        q1 = self.quater(1)
        q2 = self.quater(2)
        q3 = self.quater(3)

        eq0 = f"{f} - {h0} - {h1} * {B2},\n"
        eq1 = f"{h0} - {q0} - {q1} * {B},\n"
        eq2 = f"{h1} - {q2} - {q3} * {B},\n"
        return eq0 + eq1 + eq2

    def get_vars(self):
        return [self.full(), self.half(0), self.half(1), self.quater(0), self.quater(1), self.quater(2), self.quater(3)]

class Encoder:
    def __init__(self):
        self.fresh_counts = dict()

    def get_fresh(self, prefix):
        if prefix not in self.fresh_counts:
            self.fresh_counts[prefix] = 0
        else:
            self.fresh_counts[prefix] += 1
        return f"{prefix}_{self.fresh_counts[prefix]}"

    def encode_mulqacc(self, zero, x, qx, y, qy, shift, acc_old, acc_new):
        assert isinstance(x, FullWord)
        assert isinstance(y, FullWord)

        qx = x.quater(qx)
        qy = y.quater(qy)

        product = f"{qx} * {qy}"
        shifted = product

        if shift == 1:
            shifted = f"{product} * B"
        elif shift == 2:
            shifted = f"{product} * B^2"
        elif shift == 3:
            shifted = f"{product} * B^3"
        else:
            assert shift == 0

        if zero:
            print(f"{acc_new} - {shifted},")
        else:
            overflow = self.get_fresh("k")
            print(f"{acc_new} - {acc_old} - {shifted} - {overflow} * B^4,")

e = Encoder()
w28 = FullWord("w28")
w29 = FullWord("w29")

vars = w28.get_vars() + w29.get_vars()
print("ring r=integer,(", end="")
print(", ".join(vars + ["wacc_g1", "wacc_g2", "wacc_g3", "wacc_g4"]), end="")
print("),lp;")
print("")

print("ideal I =")
print(w28.get_equations())
print(w29.get_equations())

e.encode_mulqacc(True,  w28, 0, w29, 0, 0, None, "wacc_g1")
e.encode_mulqacc(False, w28, 1, w29, 0, 1, "wacc_g1", "wacc_g2")
e.encode_mulqacc(False, w28, 0, w29, 1, 1, "wacc_g2", "wacc_g3")
e.encode_mulqacc(False, w28, 1, w29, 1, 2, "wacc_g3", "wacc_g4")

"""
ring r=integer,(xhi, xlo, yhi, ylo, k1, k2, k3, k4, k5, t1, t2, t3, t4, B),lp;
ideal I =
    t1 - ((xhi * B + xlo) * (yhi * B + ylo)) + k4 * (B * B),
    t2 - ((xlo * ylo) + t3 * B + t4 * B) + k5 * (B * B),
    t3 - (xhi * ylo) + k1 * B,
    t4 - (xlo * yhi) + k2 * B,
    B * B;

ideal G = groebner(I);
reduce(t1 - t2, G);
"""