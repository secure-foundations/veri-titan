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
# solve(query)


x = Int('x')
y = BitVec('y', 32)

prove(
    Implies(
        And(
            x <= 0x7fffffff,
            x >= 0,
            y == (Int2BV(x, 32) >> 16),
        ),
        y <= 0x7fffffff,
    )
)

prove(
    Implies(
        And(
            x <= 0x7fffffff,
            x >= 0,
            y == (Int2BV(x, 32) >> 16),
        ),
        BV2Int(y) <= 0x7fffffff,
    )
)

# x = Int('x')
# y = Int('y')
# prove(
#     Implies(
#         And(
#             x < 115792089237316195423570985008687907853269984665640564039457584007913129639936,
#             x >= 0,
#             y == BV2Int(Int2BV(x, 256) >> 128),
#         ),
#         y < 340282366920938463463374607431768211456,
#     )
# )