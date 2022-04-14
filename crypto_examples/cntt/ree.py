# from ast import literal_eval
import random, math

from numpy import polysub, save

Q = 12289
N = 16
PSI = 1212
OMEGA = 6553

def log2(num):
    r = math.log(num, 2)
    assert r % 1.0 == 0
    return int(r)

LOGN = log2(N)
DLOGN = log2(N * 2)
LG_FMT = "0%db" % LOGN
DLG_FMT = "0%db" % DLOGN

assert pow(PSI, N * 2, Q) == 1
assert pow(OMEGA, N * 2, Q) == 1

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

def scale_poly(p):
    r = []
    for i, a in enumerate(p):
        r.append(pow(PSI, i, Q) * a % Q)
    return r

def even_poly(p):
    r = []
    # assert len(p) % 2 == 0
    for i, a in enumerate(p):
        if i % 2 == 0:
            r.append(a)
    return r

def odd_poly(p):
    r = []
    # assert len(p) % 2 == 0
    for i, a in enumerate(p):
        if i % 2 == 1:
            r.append(a)
    return r

def eval_poly(p, x):
    v = 0
    for coeff in p[::-1]:
        v = (v * x + coeff) % Q
    return v

def mod_sqr(x):
    return (x * x) % Q

poly = [1371,8801,5676,4025,3388,10753,6940,10684,10682,2458,679,11161,3648,5512,10142,10189]

# poly = [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]

saved = poly[::]
# scaled = scale_poly(poly)

def find_exp(p, y):
    results = []
    for i in range(2 * N):
        x = pow(PSI, i, Q)
        if eval_poly(p, x) == y:
            # print(format(i, fmt))
            results += [i]
    assert False

def split_eval_debug(p, x):
    sqr = (x * x) % Q
    ve = eval_poly(even_poly(p), sqr)
    vo = eval_poly(odd_poly(p), sqr)
    v = (ve + vo * x) % Q
    assert v == eval_poly(p, x)
    return (ve, vo, vo * x, v)

rev_shoup_scaled_ntt16_12289 = [0,  1479,  4043,  7143,  6553,  8155, 10984, 11567, 1212, 10643,  9094,  5860,  3542,  3504,  3621,  9744]

def build_level_poly_aux(last):
    curr = []
    if len(last) == N / 2:
        for poly in last:
            curr += [[poly[0]], [poly[1]]]
        return curr
    for poly in last:
        curr += [even_poly(poly), odd_poly(poly)]
    return curr

def build_level_polys():
    assert len(saved) == N
    curr = [list(saved)]
    level_polys = [curr]
    for _ in range(LOGN):
        curr = build_level_poly_aux(curr)
        level_polys += [curr]
    return level_polys

def x_value(i, d):
    logn = LOGN - log2(d)
    return (pow(OMEGA, d * bit_rev_int(i, logn), Q) * pow(PSI, d, Q)) % Q

def check_prefix_block(block, poly, l, d):
    assert l <= len(block) == len(poly)

    for i in range(l):
        x = x_value(i, d)
        de, do, pd, dv = split_eval_debug(poly, x)
        assert dv == block[i]
        # (v, (ve, vo, w, tp)) = block[i]
        # print("e: %d o: %d v: %d"  % (ve, vo, v))
        # assert de == ve and do == vo and dv == v

def check_suffix_block(block, poly, l, d):
    assert l <= len(block) == len(poly)
    for i in range(l, len(block)):
        x = x_value(i, d)
        de, do, pd, dv = split_eval_debug(poly, x)
        assert dv == block[i]

def check_block(block, poly, d):
    assert len(block) == len(poly)
    check_prefix_block(block, poly, len(poly), d)

level_polys = build_level_polys()
# print(len(level_polys))
for lp in level_polys:
    print(lp)

def read_as_blocks(a, d):
    blocks = []
    sz = N / d
    for i in range(d):
        block = [a[i + j * d] for j in range(sz)]
        blocks.append(block)
    return blocks

def check_t_loop_inv(a, d):
    lgd = log2(d)
    polys = level_polys[lgd]
    blocks = read_as_blocks(a, d)
    for i in range(d):
        check_block(blocks[i], polys[bit_rev_int(i, lgd)], d)

    
def check_j_loop_inv(a, d, j):
    lgd = log2(d)
    polys = level_polys[lgd]
    blocks = read_as_blocks(a, d)

    # current level has d blocks
    # each block is valid [0..2*j]
    for i in range(d):
        check_prefix_block(blocks[i], polys[bit_rev_int(i, lgd)], 2*j, d)

    # previous level has 2d blocks
    # each block is valid [j..]
    s_d = d * 2
    s_blocks = read_as_blocks(a, s_d)
    s_lgd = log2(s_d)
    s_polys = level_polys[s_lgd]
    for i in range(d * 2):
        check_suffix_block(s_blocks[i], s_polys[bit_rev_int(i, s_lgd)], j, s_d)

def check_s_loop_inv(a, d, j, bi):
    lgd = log2(d)
    polys = level_polys[lgd]
    blocks = read_as_blocks(a, d)
    # current level has d blocks
    # bi is the working block
    # advances 2 indicies
    for i in range(bi):
        check_prefix_block(blocks[i], polys[bit_rev_int(i, lgd)], 2*j+2, d)
    for i in range(bi, d):
        check_prefix_block(blocks[i], polys[bit_rev_int(i, lgd)], 2*j, d)

    # previous level has 2d blocks
    # bi and bi + d are the working blocks
    # advance 1 index each
    s_d = d * 2
    s_blocks = read_as_blocks(a, s_d)
    s_lgd = log2(s_d)
    s_polys = level_polys[s_lgd]

    for i in range(bi):
        check_suffix_block(s_blocks[i], s_polys[bit_rev_int(i, s_lgd)], j+1, s_d) 
    for i in range(bi, d):
        check_suffix_block(s_blocks[i], s_polys[bit_rev_int(i, s_lgd)], j, s_d)
    for i in range(d, bi+d):
        check_suffix_block(s_blocks[i], s_polys[bit_rev_int(i, s_lgd)], j+1, s_d) 
    for i in range(bi+d, 2*d):
        check_suffix_block(s_blocks[i], s_polys[bit_rev_int(i, s_lgd)], j, s_d) 

def mulntt_ct_std2rev_aug(a, p):
    d = N
    t = 1

    while t < N:
        p_d = d
        p_lgd = log2(p_d)
        p_blocks = read_as_blocks(a, p_d)
        p_polys = level_polys[p_lgd]
        check_t_loop_inv(a, d)

        d = int(d / 2)

        lgd = log2(d)
        lgt = LOGN - lgd - 1

        polys = level_polys[lgd]

        assert (d * 2 * t == N)
        assert (lgt == int(math.log(t, 2)))

        for j in range(t):
            check_j_loop_inv(a, d, j)
    
            w = p[t + j]
            u = 2 * d * j

            # x = (pow(OMEGA, d * bit_rev_int(2*j+1, lgt+1), Q) * pow(PSI, d, Q)) % Q
            x_e = x_value(2*j, d)
            x_o = x_value(2*j+1, d)
            assert x_e == w
            assert x_o == Q - w
            assert (x_e * x_e) % Q == (x_o * x_o) % Q == x_value(j, d * 2)

            for s in range(u, u + d):
                check_s_loop_inv(a, d, j, s-u)

                e, o = a[s], a[s + d]

                x = (o * w) % Q
                a[s + d] = (e - x) % Q
                a[s] = (e + x) % Q

                # x = (pow(OMEGA, d * bit_rev_int(2*j, lgt+1), Q) * pow(PSI, d, Q)) % Q
                # assert x == w
                # dee, deo, _, dev  = split_eval_debug(poly, x)
            
                # assert(even_poly(poly) == p_polys[2 * bit_rev_int(s-u, lgd)])
                # # assert(even_poly(poly) == last_polys[2 * bit_rev_int(s-u, lgd)])

                # doe, doo, _, dov = split_eval_debug(poly, x)
   
                # assert dee == doe == e == p_blocks[s-u][j]
                # assert deo == doo == o == p_blocks[s-u+d][j]
                # assert dev == a[s]
                # assert dov == a[s+d]
                check_s_loop_inv(a, d, j, s-u+1)
            check_j_loop_inv(a, d, j+1)

        # d is already updated
        check_t_loop_inv(a, d)

        t = t * 2

mulntt_ct_std2rev_aug(poly, rev_shoup_scaled_ntt16_12289)

# for polys in build_level_polys_rev():
#     print(polys)