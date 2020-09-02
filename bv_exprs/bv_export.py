from z3 import *
import sys

try:
	full_bits = int(sys.argv[2])
except:
	full_bits = 2

x = BitVec("x", full_bits)
y = BitVec("y", full_bits)
z = BitVec("z", full_bits)

query = (
    Implies(
        x * z == y * z,
        x == y,
    )
)
# describe_tactics()
a = Tactic("bit-blast")(query)
# a = Tactic("tseitin-cnf")(query)
print(a)
# prove(query)