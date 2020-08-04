num_bits = 64
BASE = 2 ** num_bits

def print_bin(num):
    print(bin(num)[2:][-num_bits:].zfill(num_bits))


def d0inv(w28):
    w0 = 2
    w29 = 1

    for i in range(1, num_bits):

        x = w29 * w28

        w1 = (w28 * w29) % BASE
        w1 = w1 & w0

        # q = x // 2 ** i
        # assert ((w1 == 0) == (q % 2 == 0))

        if w1 == 0:
            # print_bin(x)
            # print_bin(1 << i)
            # print_bin(1 << (i + 1))

            assert(x % (1 << i) == 1)
            # ==> 
            assert(x % (1 << (i + 1)) == 1)
        else:
            # print_bin(x)
            # print_bin(1 << i)
            # # print_bin(1 << (i + 1))
            # print()

            assert(x % (1 << i) == 1)
            # ==>
            assert((x + w28 * (1 << i)) % (1 << (i + 1)) == 1)

        w29 = w29 | w1
        w0 = w0 * 2
        assert((w29 * w28) % w0 == 1)

    assert((w29 * w28) % BASE == 1)

d0inv(2109612375)

from z3 import *

x = BitVec("x", num_bits)
i = BitVec("i", num_bits)

query = Implies(
    And(
        0 <= i,
        i < num_bits,
        URem(x, (1 << i)) == 1,
        x & (1 << i) == 0,
    ),
    URem(x, (1 << (i + 1))) == 1,
)
prove(query)

w28 = BitVec("w28", num_bits)

query = Implies(
    And(
        0 <= i,
        i < num_bits,
        URem(x, (1 << i)) == 1,
        x & (1 << i) == 1,
        URem(w28, 2) == 1,
    ),
    URem(x + w28 * (1 << i), (1 << (i + 1))) == 1,
)
prove(query)

