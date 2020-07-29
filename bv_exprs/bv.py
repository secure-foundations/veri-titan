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

def bv2int_test(bits):
    full = int(2 ** bits)
    shift = int(bits / 2)
    half = int(2 ** shift)
    mask = half - 1

    x = BitVec('x', bits)
    y = BitVec('y', bits)
    z = BitVec('z', bits)
    lh = BitVec('lh', bits)
    uh = BitVec('uh', bits)

    query = Implies(
                And(
                    x == y * z,
                    lh == x & mask,
                    uh == LShR(x, shift),
                ),
                BV2Int(uh * half + lh) == BV2Int(y * z),
            )
    prove(query)

def int2bv2int_test(bits):
    full = int(2 ** bits)
    shift = int(bits / 2)
    half = int(2 ** shift)
    mask = half - 1

    # bv only
    bvx = BitVec('x', bits)
    query = (bvx == LShR(bvx, shift) * half + (bvx & mask))
    prove(query)

    # int2bv
    x = Int('x')
    query = Implies(
                And(
                    0 <= x, x < full,
                ),
                Int2BV(x, bits) == LShR(Int2BV(x, bits), shift) * half + (Int2BV(x, bits) & mask)
            )
    prove(query)

    # treat the bit shift as mask as div and mod
    query = Implies(
                And(
                    0 <= x, x < full,
                ),
                x == (x / half) * half + x % half
            )
    prove(query)

    # int2bv then back
    query = Implies(
                And(
                    0 <= x, x < full,
                ),
                x == BV2Int(LShR(Int2BV(x, bits), shift)) * half + BV2Int(Int2BV(x, bits) & mask)
            )
    prove(query)

# bv2int_test(256)
# int2bv2int_test(32)

def misc_test():
    # forall x:bv256 :: and(x, 7) == 0 ==> mod(x, 4) == 0
    x = BitVec("x", 256)
    query = Implies(
        x & 7 == 0,
        x % 4 == 0
    )
    prove(query)

    # forall amt:bv256 :: 0 <= amt < 256 ==> Shl(1, amt) > 0
    amt = BitVec("amt", 256)
    query = Implies(
        And(0 <= amt,
            amt < 256,
        ),
        UGT(1 << amt, 0),
    )
    prove(query)

    # forall x:bv256, y:bv256, z:bv256:: $xor(x, $xor(y,z)) == $xor(y, $xor(x,z)));
    y = BitVec("y", 256)
    z = BitVec("z", 256)
    query = (
        x ^ (y ^ z) == y ^ (x ^ z)
    )
    prove(query)

    # forall x:bv256, y:bv256, z:bv256:: ($xor(x,z) == $xor(y,z)) ==> (x == y)
    query = (
        Implies(
            x ^ z == y ^ z,
            x == y,
        )
    )
    prove(query)

    # forall x:bv256 :: 0 <= and(x, 0xffff) < 0x10000
    query = (
        And(
            0 <= x & 0xffff,
            x & 0xffff < 0x10000,
        )
    )
    prove(query)

    # forall x:bv256, y:bv256, m:bv256:: m != 0 && m*x == m*y ==> x = y
    n_bits = 32
    half = int(2 ** (n_bits / 2))
    m = BitVec("m", n_bits)
    x = BitVec("x", n_bits)
    y = BitVec("y", n_bits)

    query = (
        Implies(
            And(
                0 <= x, x < half,
                0 <= y, y < half,
                0 <= m, m < half,

                m != 0,
                x * m == y * m,
            ),
            x == y,
        )
    )
    prove(query)


def mul(x, y):
    return x * y

def mulhu(x, y, bits):
    p = x * y
    return Extract(bits * 2 - 1, bits, p)
    # return LShR(p, bits)

def div(x, y):
    return x / y

def rem(x, y):
    return x % y

full_bits = 32
half_bits = int(full_bits / 2)

x = BitVec('x', full_bits)
y = BitVec('y', full_bits)

xlo = BitVec('xlo', full_bits)
xhi = BitVec('xhi', full_bits)

ylo = BitVec('ylo', full_bits)
yhi = BitVec('yhi', full_bits)

# query = (mul(x, y) == mul(y, x))
# prove(query)

query = (mulhu(x, y, half_bits) == mulhu(y, x, half_bits))
prove(query)

x = Int("x")
y = Int("y")

query = Implies(
    And(
        y > 0,
        x > y,
    ),
    rem(x, y) == x - mul(div(x, y), y),
)
prove(query)

# print(mulhu(xlo, ylo, half_bits))

# query = (
#     Implies(
#         And(
#             Extract(full_bits-1, half_bits, x) == Extract(half_bits-1, 0, xhi),
#             Extract(half_bits-1, 0, x) == Extract(half_bits-1, 0, xlo),
#             Extract(full_bits-1, half_bits, y) == Extract(half_bits-1, 0, yhi),
#             Extract(half_bits-1, 0, y) == Extract(half_bits-1, 0, ylo),
#         ),
#         (mul(x, y) == mulhu(xlo, ylo, half_bits)
#             + mul(xhi, ylo)
#             + mul(xlo, yhi)
#             + mul(xlo, ylo) 
#         ),
#     )
# )
# prove(query)