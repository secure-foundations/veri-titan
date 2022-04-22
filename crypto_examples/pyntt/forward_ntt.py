from sympy import mod_inverse
from polys import *

class ForwardNTT:
    def __init__(self, q, n, psi, omega):
        self.Q = q
        self.N = n
        self.PSI = psi
        self.OMEGA = omega
        self.LOGN = log2(self.N)
        self.R = 2 ** 16
        self.R_INV = mod_inverse(2 ** 16, self.Q)

        assert ((self.R * self.R_INV) % self.Q == 1)
        assert pow(self.PSI, self.N * 2, self.Q) == 1
        assert pow(self.OMEGA, self.N * 2, self.Q) == 1

    def montmul(self, a, b):
        return (a * b * self.R_INV) % self.Q

    def x_value(self, i, d):
        logn = self.LOGN - log2(d)
        return (pow(self.OMEGA, d * bit_rev_int(i, logn), self.Q) * pow(self.PSI, d, self.Q)) % self.Q

    def read_as_blocks(self, a, d):
        blocks = []
        sz = self.N / d
        for i in range(d):
            block = [a[i + j * d] for j in range(sz)]
            blocks.append(block)
        return blocks

    def check_prefix_block(self, block, poly, l, d):
        assert l <= len(block) == len(poly)
        for i in range(l):
            x = self.x_value(i, d)
            assert block[i] == poly.eval(x)

    def check_suffix_block(self, block, poly, l, d):
        assert l <= len(block) == len(poly)
        for i in range(l, len(block)):
            x = self.x_value(i, d)
            assert block[i] == poly.eval(x)

    def check_block(self, block, poly, d):
        assert len(block) == len(poly)
        self.check_prefix_block(block, poly, len(poly), d)

    def check_t_loop_inv(self, a, d):
        if self.disable_checks:
            return

        lgd = log2(d)
        polys = self.level_polys[lgd]
        blocks = self.read_as_blocks(a, d)
        for i in range(d):
            self.check_block(blocks[i], polys[bit_rev_int(i, lgd)], d)
        
    def check_j_loop_inv(self, a, d, j):
        if self.disable_checks:
            return

        lgd = log2(d)
        polys = self.level_polys[lgd]
        blocks = self.read_as_blocks(a, d)

        # current level has d blocks
        # each block is valid [0..2*j]
        for i in range(d):
            self.check_prefix_block(blocks[i], polys[bit_rev_int(i, lgd)], 2*j, d)

        # previous level has 2d blocks
        # each block is valid [j..]
        s_d = d * 2
        s_blocks = self.read_as_blocks(a, s_d)
        s_lgd = log2(s_d)
        s_polys = self.level_polys[s_lgd]
        for i in range(d * 2):
            self.check_suffix_block(s_blocks[i], s_polys[bit_rev_int(i, s_lgd)], j, s_d)

    def check_s_loop_inv(self, a, d, j, bi):
        if self.disable_checks:
            return
        lgd = log2(d)
        polys = self.level_polys[lgd]
        blocks = self.read_as_blocks(a, d)
        # current level has d blocks
        # bi is the working block
        # advances 2 indicies
        for i in range(bi):
            self.check_prefix_block(blocks[i], polys[bit_rev_int(i, lgd)], 2*j+2, d)
        for i in range(bi, d):
            self.check_prefix_block(blocks[i], polys[bit_rev_int(i, lgd)], 2*j, d)

        # previous level has 2d blocks
        # bi and bi + d are the working blocks
        # advance 1 index each
        s_d = d * 2
        s_blocks = self.read_as_blocks(a, s_d)
        s_lgd = log2(s_d)
        s_polys = self.level_polys[s_lgd]

        for i in range(bi):
            self.check_suffix_block(s_blocks[i], s_polys[bit_rev_int(i, s_lgd)], j+1, s_d) 
        for i in range(bi, d):
            self.check_suffix_block(s_blocks[i], s_polys[bit_rev_int(i, s_lgd)], j, s_d)
        for i in range(d, bi+d):
            self.check_suffix_block(s_blocks[i], s_polys[bit_rev_int(i, s_lgd)], j+1, s_d) 
        for i in range(bi+d, 2*d):
            self.check_suffix_block(s_blocks[i], s_polys[bit_rev_int(i, s_lgd)], j, s_d) 

    def check_twiddle_factors(self, p):
        assert len(p) == self.N
        t = 1
        while t < self.N:
            for j in range(t):
                d = self.N / (t * 2)
                assert p[t+j] == (self.x_value(2*j, d) * self.R) % self.Q
            t = t * 2

    def mulntt_ct_std2rev(self, a, p, disable_checks=False):
        self.check_twiddle_factors(p)
        self.disable_checks = disable_checks

        assert len(a) == len(p) == self.N
        self.saved = ModQPoly(a, self.Q)
        self.level_polys = build_level_polys(self.saved)

        d = self.N
        t = 1

        while t < self.N:
            self.check_t_loop_inv(a, d)

            d = int(d / 2)

            lgd = log2(d)
            lgt = self.LOGN - lgd - 1

            # assert (d * 2 * t == self.N)
            # assert (lgt == log2(t))

            for j in range(t):
                self.check_j_loop_inv(a, d, j)
        
                w = p[t + j]
                u = 2 * d * j
                # assert w == self.x_value(2*j, d)
                # w_r = (w * self.R) % self.Q

                # x = (pow(OMEGA, d * bit_rev_int(2*j+1, lgt+1), Q) * pow(PSI, d, Q)) % Q
                # x_e = self.x_value(2*j, d)
                # x_o = self.x_value(2*j+1, d)
                # assert x_e == w
                # assert x_o == self.Q - w
                # assert (x_e * x_e) % self.Q == (x_o * x_o) % self.Q == x_value(j, d * 2)

                for s in range(u, u + d):
                    self.check_s_loop_inv(a, d, j, s-u)

                    e, o = a[s], a[s + d]

                    x = self.montmul(o, w)
                    a[s + d] = (e - x) % self.Q
                    a[s] = (e + x) % self.Q

                    # x = (pow(OMEGA, d * bit_rev_int(2*j, lgt+1), Q) * pow(PSI, d, Q)) % Q
                    # assert x == w
                    # dee, deo, _, dev  = split_eval_debug(poly, x)
                
                    # assert(even_poly(poly) == p_polys[2 * bit_rev_int(s-u, lgd)])
                    # assert(even_poly(poly) == last_polys[2 * bit_rev_int(s-u, lgd)])

                    # doe, doo, _, dov = split_eval_debug(poly, x)
    
                    # assert dee == doe == e == p_blocks[s-u][j]
                    # assert deo == doo == o == p_blocks[s-u+d][j]
                    # assert dev == a[s]
                    # assert dov == a[s+d]
    
                    self.check_s_loop_inv(a, d, j, s-u+1)
                self.check_j_loop_inv(a, d, j+1)

            # d is already updated
            self.check_t_loop_inv(a, d)
            t = t * 2

        # always do this check
        for i in range(self.N):
            x = self.x_value(i, 1)
            assert self.saved.eval(x) == a[i]
        print("final check done")