import random


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

assert mul_lh_bb(xhi * B + xlo, yhi * B + ylo) == (xlo * ylo + 
    mul_lh_b(xhi, ylo) * B + \
    mul_lh_b(xlo, yhi) * B) % (B * B)

# assert (xhi * B + xlo) * (yhi * B + ylo) == (mul_lh_b(xlo, ylo) + \
#     mul_uh_b(xlo, ylo) * B + \
#     mul_lh_b(xhi, ylo) * B + \
#     mul_lh_b(xlo, yhi) * B) % (B * B)
