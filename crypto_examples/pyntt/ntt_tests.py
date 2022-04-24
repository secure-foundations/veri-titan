from forward_ntt import *
from inverse_ntt import *

Q = 12289
N = 512
PSI = 1003

poly1 = generate_random_poly(N, Q)
poly2 = generate_random_poly(N, Q)
product = reference_poly_mul(poly1, poly2, Q)

fntt16 = ForwardNTT(N, Q, PSI, 16)
points1 = fntt16.mulntt_ct_std2rev(poly1, True)

fntt16 = ForwardNTT(N, Q, PSI, 16)
points2 = fntt16.mulntt_ct_std2rev(poly2, True)

points3 = []
for i in range(len(points1)):
    points3.append((points1[i] * points2[i]) % Q)

intt16 = InverseNTT(N, Q, PSI, 16)
poly3 = ModQPoly(bit_rev_shuffle(points3), Q)
points4 = intt16.intt(poly3, True)

factors = intt16.build_intt_scalling_table()
for i in range(len(points4)):
    points4[i] = intt16.montmul(points4[i], factors[i])

for i in range(N):
    assert points4[i] == product[i]
