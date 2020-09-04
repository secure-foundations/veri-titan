import os
import pyboolector
from pyboolector import Boolector, BoolectorException
from pyboolector import BTOR_OPT_PRINT_DIMACS, BTOR_OPT_MODEL_GEN

import sys

try:
	full_bits = int(sys.argv[2])
except:
	full_bits = 3

def prove(btor, x):
	btor.Assert(btor.Not(x))
	r = btor.Sat()
	if r == Boolector.UNSAT:
		print("proved")
	elif r == Boolector.SAT:
		print("falsified")
	else:
		assert r == Boolector.UNKNOWN
		print("unknown")

def check(btor, x):
	btor.Assert(x)
	return print_result(btor.Sat())

half_bits = int(full_bits / 2)
BASE = 2 ** full_bits
HALF_BASE = int(2 ** half_bits)

btor = Boolector()

full_sort = btor.BitVecSort(full_bits)
half_sort = btor.BitVecSort(half_bits)

# btor.Set_opt(BTOR_OPT_EXIT_CODES, 1)
# btor.Set_opt(BTOR_OPT_MODEL_GEN, 1)
btor.Set_opt(BTOR_OPT_PRINT_DIMACS, 1) # enabling this causes Sat() to return UNKNOWN

x = btor.Var(full_sort, "x")
y = btor.Var(full_sort, "y")
z = btor.Var(full_sort, "z")

q = btor.Implies(
	x ^ z == y ^ z,
	x == y,
)

prove(btor, q)
# print(check(btor, q))