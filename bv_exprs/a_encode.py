import random

# print("B4 == B ^ 4")

# def encode_qmul(x, ):
	# function {:opaque} uint256_qsel(x: uint256, qx: uint2): uint64
	# {
	# 	if qx == 0 then
	# 		x % BASE_64
	# 	else if qx == 1 then
	# 		(x / BASE_64) % BASE_64
	# 	else if qx == 1 then
	# 		(x / BASE_128) % BASE_64
	# 	else
	# 		(x / BASE_192) % BASE_64
	# }

# def encode_mulquacc(zero, x, qx, y, qy, shift, acc):
	# var product := uint256_qmul(x, qx, y, qy);
	# var shift := uint256_ls(product, shift * 8);
	# if zero then shift else (acc + shift) % BASE_256

    # requires pc1: wacc_g1 == mulqacc256(true, w28, 0, w29, 0, 0, 0);
    # requires pc2: wacc_g2 == mulqacc256(false, w28, 1, w29, 0, 1, wacc_g1);
    # requires pc3: result_g1 == mulqacc256(false, w28, 0, w29, 1, 1, wacc_g2)
    # 	&& wacc_g3 == uint256_uh(result_g1)
    # 	&& w1_g2 == uint256_hwb(w1_g1, uint256_lh(result_g1), true);
    # requires pc4: wacc_g4 == mulqacc256(false, w28, 2, w29, 0, 0, wacc_g3);
    # requires pc5: wacc_g5 == mulqacc256(false, w28, 1, w29, 1, 0, wacc_g4);
    # requires pc6: wacc_g6 == mulqacc256(false, w28, 0, w29, 2, 0, wacc_g5);
    # requires pc7: wacc_g7 == mulqacc256(false, w28, 3, w29, 0, 1, wacc_g6);
    # requires pc8: wacc_g8 == mulqacc256(false, w28, 2, w29, 1, 1, wacc_g7);
    # requires pc9: wacc_g9 == mulqacc256(false, w28, 1, w29, 2, 1, wacc_g8);
    # requires pc10: result_g2 == mulqacc256(false, w28, 0, w29, 3, 1, wacc_g9)
    # 	&& w1 == uint256_hwb(w1_g2, uint256_lh(result_g2), false);
    # ensures half_product(w1, w28, w29);

B = 2 ** 10
xlo = random.randint(0, B-1)
xhi = random.randint(0, B-1)

ylo = random.randint(0, B-1)
yhi = random.randint(0, B-1)

def mul_lh_b(a, b):
	return (a * b) % B

def mul_uh_b(a, b):
	return (a * b) // B

def mul_lh_bb(a, b):
	return (a * b) % (B * B)

assert mul_lh_bb(xhi * B + xlo, yhi * B + ylo) == (mul_lh_b(xlo, ylo) + \
    mul_uh_b(xlo, ylo) * B + \
    mul_lh_b(xhi, ylo) * B + \
    mul_lh_b(xlo, yhi) * B) % (B * B)

# assert mul_lh_bb(xhi * B + xlo, yhi * B + ylo) == (xlo * ylo + 
#     mul_lh_b(xhi, ylo) * B + \
#     mul_lh_b(xlo, yhi) * B) % (B * B)

# assert ((xhi * B + xlo) * (yhi * B + ylo)) % (B * B) == (mul_lh_b(xlo, ylo) + \
#     mul_uh_b(xlo, ylo) * B + \
#     mul_lh_b(xhi, ylo) * B + \
#     mul_lh_b(xlo, yhi) * B) % (B * B)

assert ((xhi * B + xlo) * (yhi * B + ylo)) % (B * B) == ((xlo * ylo) % B + \
    (xlo * ylo) // B * B + \
    (xhi * ylo) % B * B + \
    (xlo * yhi) % B * B) % (B * B)

assert ((xhi * B + xlo) * (yhi * B + ylo)) % (B * B) == ((xlo * ylo) + (xhi * ylo) % B * B + (xlo * yhi) % B * B) % (B * B)

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