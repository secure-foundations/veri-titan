from sympy import mod_inverse
import math

def log2(num):
    r = math.log(num, 2)
    assert r % 1.0 == 0
    return int(r)

# modder = lambda t: t % Q

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

def bit_rev_shuffle(a):
    n = len(a)
    logn = log2(n)
    c = [0 for i in range(n)]
    for i in range(n):
        c[bit_rev_int(i, logn)] = a[i]
    return c

def check_nth_primitive_root(r, n, q):
    if pow(r, n, q) != 1:
        return False
    for j in range(1, n):
        if pow(r, j, q) == 1:
            return False
    return True

def find_nth_primitive_root(n, q):
    for r in range(q):
        if check_nth_primitive_root(r, n, q):
            return r
    assert False

class NTTConsts:
    def __init__(self, n, q, bits):
        self.N = n
        self.LOGN = log2(self.N)
        self.Q = q
        self.R = 2 ** bits
        self.R_INV = mod_inverse(self.R, q)

        self.PSI = find_nth_primitive_root(2 * n, q)
        assert(check_nth_primitive_root(self.PSI, 2 * n, q))
        self.PSI_INV = mod_inverse(self.PSI, q)

        self.OMEGA = find_nth_primitive_root(n, q)
        assert(check_nth_primitive_root(self.OMEGA, n, q))
        self.OMEGA_INV = mod_inverse(self.OMEGA, q)

        self.N_INV = mod_inverse(self.N, q)
        self.RR = (self.R * self.R) % q

    def montmul(self, a, b):
        return (a * b * self.R_INV) % self.Q

    def build_rev_mixed_powers_mont_table(self):
        result = [0 for i in range(self.N)]
        t = 1
        while t < self.N:
            for j in range(t):
                d = self.N / (t * 2)
                logn = self.LOGN - log2(d)
                value = (pow(self.OMEGA, d * bit_rev_int(2 * j, logn), self.Q) * pow(self.PSI, d, self.Q) * self.R) % self.Q
                result[t+j] = value
            t = t * 2
        return result

    def build_rev_omega_inv_powers_mont_table(self):
        result = [0 for i in range(self.N)]
        t = 1
        while t < self.N:
            for j in range(t):
                d = self.N / (t * 2)
                logn = self.LOGN - log2(d)
                value = (pow(self.OMEGA_INV, d * bit_rev_int(2 * j, logn), self.Q) * self.R) % self.Q
                result[t+j] = value
            t = t * 2
        return result

    def build_intt_scalling_table(self):
        result = []
        for i in range(self.N):
            # when multiplying this is already in montgomery form
            value = (pow(self.PSI_INV, i, self.Q) * self.N_INV * self.R) % self.Q
            result.append(value)
        return result

if __name__ == "__main__":
    Q = 12289
    # nttconst = NTTConsts(16, Q, 1212, 16)
    # NTTConsts(256, Q, 1002, 16)
    nttconst = NTTConsts(512, Q, 16)
    print(nttconst.build_rev_mixed_powers_mont_table())
    print(nttconst.build_intt_scalling_table())

    # NTTConsts(1024, Q, 1014, 16)
