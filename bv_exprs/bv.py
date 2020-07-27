from z3 import *


def pure_bv_test():
    x = BitVec('x', 256)
    y = BitVec('y', 256)
    z = BitVec('z', 256)
    lh = BitVec('lh', 256)
    uh = BitVec('uh', 256)

    prove(
        x == LShR(x, 128) * 340282366920938463463374607431768211456 + (x & 340282366920938463463374607431768211455)
    )

    query = Implies(
                And(
                    x == y * z,
                    lh == x & 340282366920938463463374607431768211455,
                    uh == LShR(x, 128),
                ),
                uh * 340282366920938463463374607431768211456 + lh == y * z,
            )

    prove(query)

def bv2int_test():
    x = BitVec('x', 256)
    y = BitVec('y', 256)
    z = BitVec('z', 256)
    lh = BitVec('lh', 256)
    uh = BitVec('uh', 256)

    query = Implies(
                And(
                    x == y * z,
                    lh == x & 340282366920938463463374607431768211455,
                    uh == LShR(x, 128),
                ),
                BV2Int(uh * 340282366920938463463374607431768211456 + lh) == BV2Int(y * z),
            )
    prove(query)

def int2bv2int_test():
    x = Int('x')
    y = Int('y')
    z = Int('z')
    lh = Int('lh')
    uh = Int('uh')

    query = Implies(
                And(
                    0 <= y,
                    y < 340282366920938463463374607431768211456,
                    0 <= z,
                    z < 340282366920938463463374607431768211456,
                    x == y * z,
                    lh == BV2Int(Int2BV(x, 256) & 340282366920938463463374607431768211455),
                    uh == BV2Int(LShR(Int2BV(x, 256), 128)),
                ),
                uh * 340282366920938463463374607431768211456 + lh == y * z,
            )
    prove(query)

pure_bv_test()
bv2int_test()
int2bv2int_test()
