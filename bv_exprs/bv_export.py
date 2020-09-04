import os
import pyboolector
from pyboolector import Boolector, BoolectorException, BTOR_OPT_PRINT_DIMACS, BTOR_OPT_MODEL_GEN

btor = Boolector()
# btor.Set_opt(BTOR_OPT_PRINT_DIMACS, 1)
btor.Set_opt(BTOR_OPT_MODEL_GEN, 1)

bv8 = btor.BitVecSort(8)

x = btor.Var(bv8, "x")
y = btor.Var(bv8, "y")

btor.Assert(0 < x)
btor.Assert(x <= 100)
btor.Assert(0 < y)
btor.Assert(y <= 100)
btor.Assert(x * y < 100)

umulo = btor.Umulo(x, y)  # overflow bit of x * y
btor.Assert(~umulo)       # do not allow overflows

result = btor.Sat()
print(x.assignment)  # prints: 00000100
print(y.assignment)  # prints: 00010101
print("{} {}".format(x.symbol, x.assignment))  # prints: x 00000100
print("{} {}".format(y.symbol, y.assignment))  # prints: y 00010101