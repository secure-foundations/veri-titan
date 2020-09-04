import os
import pyboolector
from pyboolector import Boolector, BoolectorException
from pyboolector import BTOR_OPT_PRINT_DIMACS, BTOR_OPT_MODEL_GEN

import sys

try:
	full_bits = int(sys.argv[2])
except:
	full_bits = 2

def prove(btor, x):
	btor.Assert(btor.Not(x))
	return btor.Sat() == Boolector.UNSAT

def check(btor, x):
	btor.Assert(x)
	return btor.Sat() == Boolector.SAT

half_bits = int(full_bits / 2)
BASE = 2 ** full_bits
HALF_BASE = int(2 ** half_bits)

btor = Boolector()

full_sort = btor.BitVecSort(full_bits)
half_sort = btor.BitVecSort(half_bits)

# btor.Set_opt(BTOR_OPT_EXIT_CODES, 1)
# btor.Set_opt(BTOR_OPT_MODEL_GEN, 1)
# btor.Set_opt(BTOR_OPT_PRINT_DIMACS, 1)

x = btor.Var(full_sort, "x")
y = btor.Var(full_sort, "y")
z = btor.Var(full_sort, "z")

q = btor.Implies(
		btor.And(
			x * z == y * z,
			z != 0),
		x == y
	)

print(prove(btor, q))
# print(check(btor, q))
