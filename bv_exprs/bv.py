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

def int2bv2int_test(bits):
    full = int(2 ** bits)
    shift = int(bits / 2)
    half = int(2 ** shift)
    mask = half - 1

    bvx = BitVec('x', bits)
    query = (bvx == LShR(bvx, shift) * half + (bvx & mask))
    prove(query)

    x = Int('x')
    bvx = Int2BV(x, bits)
    query = Implies(
                And(
                    0 <= x, x < full,
                ),
                bvx == LShR(bvx, shift) * half + (bvx & mask)
            )
    prove(query)

    query = Implies(
                And(
                    0 <= x, x < full,
                ),
                x == BV2Int(LShR(bvx, shift)) * half + BV2Int(bvx & mask)
            )
    prove(query)

int2bv2int_test(32)
