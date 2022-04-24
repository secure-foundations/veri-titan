from forward_ntt import *
from inverse_ntt import *

Q = 12289
N = 1024
BITS = 16

# generate inputs
poly1 = generate_random_poly(N, Q)
poly2 = generate_random_poly(N, Q)
product = reference_poly_mul(poly1, poly2, Q)

# forward transformation
fntt = ForwardNTT(N, Q, BITS)
points1 = fntt.mulntt_ct_std2rev(poly1, True)

# forward transformation
fntt = ForwardNTT(N, Q, BITS)
points2 = fntt.mulntt_ct_std2rev(poly2, True)

# currently both points are in bit rev order 

# scale first so we can use mont mul
for i in range(len(points2)):
    points2[i] = fntt.montmul(points2[i], fntt.RR)

# then actual multiplication
points3 = []
for i in range(len(points1)):
    points3.append(fntt.montmul(points1[i], points2[i]))

# inverse transformation
intt = InverseNTT(N, Q, BITS)
# shuffle the points so they are in normal order
poly3 = ModQPoly(bit_rev_shuffle(points3), Q)
points4 = intt.intt(poly3, True)

# adjust for factors
factors = intt.build_intt_scalling_table()
for i in range(len(points4)):
    points4[i] = intt.montmul(points4[i], factors[i])

# check eqal to reference
for i in range(N):
    assert points4[i] == product[i]
