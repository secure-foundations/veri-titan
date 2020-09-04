from z3 import *
import sys

try:
	full_bits = int(sys.argv[2])
except:
	full_bits = 32

half_bits = int(full_bits / 2)
BASE = 2 ** full_bits
HALF_BASE = int(2 ** half_bits)

# scales well (256 bits+)

def bvand():
	x = BitVec("x", full_bits)
	y = BitVec("y", full_bits)
	query = x & y == y & x
	prove(query)

def shift():
	amt = BitVec("amt", full_bits)
	query = Implies(
		And(0 <= amt,
			amt < full_bits,
		),
		UGT(1 << amt, 0),
	)
	prove(query)

def mul():
	x = BitVec("x", full_bits)
	y = BitVec("y", full_bits)
	z = BitVec("z", full_bits)

	query = (
		Implies(
			And(x * z == y * z,
			z != 0),
			x == y,
		)
	)
	prove(query)

def xor():
	x = BitVec("x", full_bits)
	y = BitVec("y", full_bits)
	z = BitVec("z", full_bits)

	query = (
		Implies(
			x ^ z == y ^ z,
			x == y,
		)
	)
	prove(query)

def andorxor_135():
	x = BitVec("x", full_bits)
	c1 = BitVec("c1", full_bits)
	c2 = BitVec("c2", full_bits)
	query = (x & c2) ^ (c1 & c2) == (x ^ c1) & c2
	prove(query)

def addsub_1043():
	x = BitVec("x", full_bits)
	y = BitVec("y", full_bits)
	query = 0 == ((x & y) ^ y) + 1 + (x | ~y)
	prove(query)

def addsub_1156():
	x = BitVec("x", full_bits)
	query = (x + x == (x << 1))
	prove(query)

# doesn't scale so well
def mul():
	m = BitVec("m", full_bits)
	x = BitVec("x", full_bits)
	y = BitVec("y", full_bits)

	query = (
		Implies(
			And(
				0 <= x, x < HALF_BASE,
				0 <= y, y < HALF_BASE,
				0 <= m, m < HALF_BASE,
				m != 0,
				x * m == y * m,
			),
			x == y,
		)
	)
	prove(query)

def mul_reasm():
	x = BitVec('x', full_bits)
	y = BitVec('y', full_bits)

	xlo = BitVec('xlo', half_bits)
	xhi = BitVec('xhi', half_bits)

	ylo = BitVec('ylo', half_bits)
	yhi = BitVec('yhi', half_bits)

	def mulhu(x, y, bits):
		assert(x.size() == y.size() == bits)
		extend = bits * 2
		p = ZeroExt(bits, x) * ZeroExt(bits, y)
		return Extract(extend - 1, bits, p)

	# xhi : xlo == x
	# yhi : ylo == y
	# x * y == uh(xlo, ylo) + xhi * ylo + xlo * yhi : xlo * ylo

	query = (
		Implies(
			And(
				Extract(full_bits-1, half_bits, x) == xhi,
				Extract(half_bits-1, 0, x) == xlo,
				Extract(full_bits-1, half_bits, y) == yhi,
				Extract(half_bits-1, 0, y) == ylo,
			),
			Concat(mulhu(xlo, ylo, half_bits) + xhi * ylo + xlo * yhi, xlo * ylo) == x * y
		)
	)
	prove(query)

def d0inv_1():
	x = BitVec("x", full_bits)
	i = BitVec("i", full_bits)

	query = Implies(
		And(
			0 <= i,
			i < full_bits,
			URem(x, (1 << i)) == 1,
			# x & ((1 << i) - 1) == 1,
			x & (1 << i) == 0,
		),
		URem(x, (1 << (i + 1))) == 1,
		# x & ((1 << (i + 1)) - 1) == 1,
	)
	prove(query)

def d0inv_2():
	x = BitVec("x", full_bits)
	w28 = BitVec("x", full_bits)
	i = BitVec("i", full_bits)

	query = Implies(
		And(
			0 <= i,
			i < full_bits,
			URem(x, (1 << i)) == 1,
			# x & ((1 << i) - 1) == 1,
			x & (1 << i) == (1 << i),
			w28 & 1 == 1,
		),
		URem(x + w28 * (1 << i), (1 << (i + 1))) == 1,
		# (x + (w28 << i)) & (1 << (i + 1)) - 1 == 1,
	)
	prove(query)

try:
	a = sys.argv[1] + "()"
	eval(a)
except:
	print("usage:\npython bv_exprs.py [function_name] [bit_number]")
