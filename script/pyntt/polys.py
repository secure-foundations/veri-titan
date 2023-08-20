import random
from ntt_consts import log2
import numpy as np

class ModQPoly:
    def __init__(self, coeffs, q):
        self.coeffs = list(coeffs)
        self.Q = q
    
    def __repr__(self):
        return str(self.coeffs)

    def __len__(self):
        return len(self.coeffs)

    def __getitem__(self, i):
        return self.coeffs[i]

    def eval(self, x):
        v = 0
        for coeff in self.coeffs[::-1]:
            v = (v * x + coeff) % self.Q
        return v

    def even_poly(self):
        r = []
        for i, a in enumerate(self.coeffs):
            if i % 2 == 0:
                r.append(a)
        return ModQPoly(r, self.Q)

    def odd_poly(self):
        r = []
        for i, a in enumerate(self.coeffs):
            if i % 2 == 1:
                r.append(a)
        return ModQPoly(r, self.Q)

    def mod_sqr(self, x):
        return (x * x) % self.Q

    def split_eval_debug(self, x):
        sqr = self.mod_sqr(x)
        ve = self.even_poly().eval(sqr)
        vo = self.odd_poly().eval(sqr)
        v = (ve + vo * x) % self.Q
        assert v == self.eval(x)
        return (ve, vo, vo * x, v)

def build_level_poly_aux(last):
    curr = []
    for poly in last:
        curr += [poly.even_poly(), poly.odd_poly()]
    return curr

def build_level_polys(poly):
    logn = log2(len(poly))
    curr = [poly]
    level_polys = [curr]
    for _ in range(logn):
        curr = build_level_poly_aux(curr)
        level_polys += [curr]
    return level_polys

def reference_poly_mul(p1, p2, q):
    assert len(p1) == len(p2) 

    product = np.polymul(p1.coeffs[::-1], p2.coeffs[::-1])
    product = [c % q for c in product]
    mod = [1] + [0 for _ in range(len(p1)-1)] + [1]
    assert len(mod) == len(p1) + 1
    reaminder = np.polydiv(product, mod)[1]
    reaminder = [int(c % q) for c in reaminder][::-1]
    return ModQPoly(reaminder, q)

def generate_random_poly(n, q):
    return ModQPoly([random.randint(0, q) for i in range(n)], q)

