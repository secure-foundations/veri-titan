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

    def get_equation(self):
        f = self.full()

        h0 = self.half(0)
        h1 = self.half(1)

        q0 = self.quater(0)
        q1 = self.quater(1)
        q2 = self.quater(2)
        q3 = self.quater(3)

        eq0 = f"{f} - {h0} - {h1} * {B2}\n"
        eq1 = f"{h0} - {q0} - {q1} * {B}\n"
        eq2 = f"{h1} - {q2} - {q3} * {B}\n"
        return eq0 + eq1 + eq2

class Encoder:
    def __init__(self, q):
        self.tmp_count = 0
        self.bin_count = 0
        self.k_count = 0

    # def encode_mulqacc

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