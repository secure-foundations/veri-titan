# from ast import literal_eval
import random, math

Q = 12289
N = 16
PSI = 1212
OMEGA = 6553

LOGN = int(math.log(N, 2))
DLOGN = int(math.log(N * 2, 2))
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
    r = bit_rev_str(i, lg)
    return int(r, base=2)

def scale_poly(p):
    r = []
    for i, a in enumerate(p):
        r.append(pow(PSI, i, Q) * a % Q)
    return r

def even_poly(p):
    r = []
    assert len(p) % 2 == 0
    for i, a in enumerate(p):
        if i % 2 == 0:
            r.append(a)
    return r

def odd_poly(p):
    r = []
    assert len(p) % 2 == 0
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

saved = list(poly)
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

levels = []

def mulntt_ct_std2rev(a, n, p):
    d = n
    t = 1

    while t < n:
        d = int(d / 2)
        assert (d * 2 * t == n)
  
        # print("blocks(d)=%d, size(2t)=%d" %(d, 2*t))

        sources = dict()
        for j in range(t):
            w = p[t + j]
            u = 2 * d * j
            # print("\tj=%d"  % j);
            width = math.log(n / d, 2) - 1

            # w_t = pow(OMEGA, d, Q)
            # psi_t = pow(PSI, d, Q)
            # assert(w == (psi_t * pow(w_t, bit_rev_int(j, width), Q)) % Q)
            assert(w == pow(PSI, 2 * d * bit_rev_int(j, width) + d, Q))
            for s in range(u, u + d):
                e, o = a[s], a[s + d]
                x = (o * w) % Q
                a[s + d] = (e - x) % Q
                a[s] = (e + x) % Q

                sources[a[s]] = (e, o, w, "even")
                sources[a[s+d]] = (e, o, w, "odd")
        level = []
        for i in range(d):
            values = []
            for k in range(i, i+d*(2* t), d):
                # values += [a[k]]
                values += [(a[k], sources[a[k]])]
            level.append(values)
        levels.append(level)
        t = t * 2

rev_shoup_scaled_ntt16_12289 = [0,  1479,  4043,  7143,  6553,  8155, 10984, 11567, 1212, 10643,  9094,  5860,  3542,  3504,  3621,  9744]

mulntt_ct_std2rev(poly, 16, rev_shoup_scaled_ntt16_12289)
ys = poly

levels = levels[::-1]

def build_level_poly_aux(last):
    assert len(last) <= 16
    curr = []
    for poly in last:
        curr += [even_poly(poly), odd_poly(poly)]
    return curr

def build_level_polys():
    level_polys = []
    assert len(saved) == N
    curr = [list(saved)]
    for i in range(LOGN):
        level_polys += [curr]
        curr = build_level_poly_aux(curr)
    return level_polys

polys = build_level_polys()

def check_block(block, poly):
    logn = int(math.log(len(block), 2))
    exp = pow(2, LOGN - logn)
    for i in range(len(block)):
        x = (pow(OMEGA, exp * bit_rev_int(i, logn), Q) * pow(PSI, exp, Q)) % Q
        de, do, pd, dv = split_eval_debug(poly, x)
        (v, (ve, vo, w, tp)) = block[i]
        # print("e: %d o: %d v: %d"  % (ve, vo, v))
        assert de == ve and do == vo and dv == v

# check_block(levels[0][0], polys[0][0])
# check_block(levels[1][1], polys[1][1])
# check_block(levels[1][0], polys[1][0])
# check_block(levels[2][1], polys[2][2])

def validate_level(polys, blocks):
    assert len(polys) == len(blocks)
    logc = int(math.log(len(polys), 2))
    for i in range(len(polys)):
        check_block(blocks[i], polys[bit_rev_int(i, logc)])

def validate_levels():
    level_polys = build_level_polys()
    for i in range(len(level_polys)):
        validate_level(level_polys[i], levels[i])

validate_levels()