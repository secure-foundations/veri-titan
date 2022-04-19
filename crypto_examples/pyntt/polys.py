from cmath import log
import random, math

def log2(num):
    r = math.log(num, 2)
    assert r % 1.0 == 0
    return int(r)

modder = lambda t: t % Q

def bit_rev_str(i, lg):
    fmt = "0%db" % lg
    r = format(i, fmt)[::-1]
    return r

def bit_str(i, lg):
    fmt = "0%db" % lg
    r = format(i, fmt)
    return r

def bit_rev_int(i, lg):
    assert i < pow(2, lg)
    r = bit_rev_str(i, lg)
    return int(r, base=2)

# def scale_poly(p, psi, q):
#     r = []
#     for i, a in enumerate(p):
#         r.append(pow(psi, i, q) * a % q)
#     return r

class ModQPoly:
    def __init__(self, coeffs, q):
        self.coeffs = list(coeffs)
        self.Q = q
    
    def __repr__(self):
        return str(self.coeffs)

    def __len__(self):
        return len(self.coeffs)

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

# poly = [1371,8801,5676,4025,3388,10753,6940,10684,10682,2458,679,11161,3648,5512,10142,10189]

# lpolys = build_level_polys(ModQPoly(poly, 12289))

# for i in range(len(lpolys)):
#     print(lpolys[i])

# def find_exp(p, y):
#     results = []
#     for i in range(2 * N):
#         x = pow(PSI, i, Q)
#         if eval(p, x) == y:
#             # print(format(i, fmt))
#             results += [i]
#     assert False


