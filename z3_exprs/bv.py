from z3 import *

x = BitVec('x', 256)
y = BitVec('y', 256)
z = BitVec('z', 256)
lh = BitVec('lh', 256)
uh = BitVec('uh', 256)

prove(
    x == (x >> 128) * 340282366920938463463374607431768211456 + (x & 340282366920938463463374607431768211455)
)

query = Implies(
            And(
                x == y * z,
                lh == x & 340282366920938463463374607431768211455,
                uh == x >> 128,
            ),
            uh * 340282366920938463463374607431768211456 + lh == y * z,
        )

prove(query)
solve(query)