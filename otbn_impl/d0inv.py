num_bits = 32
BASE = 2 ** num_bits

def print_bin(num):
    print(bin(num)[2:][-num_bits:].zfill(num_bits))

def d0inv(w28):
    w0 = 2
    w29 = 1

    for i in range(1, num_bits):

        x = w29 * w28
        q = x // 2 ** i

        w1 = (w28 * w29) % BASE
        w1 = w1 & w0

        assert ((w1 == 0) == (q % 2 == 0))

        if q % 2 == 0:
            # print_bin(x)
            # print_bin(q)
            # print_bin(2 ** i)
            # print_bin(2 ** (i + 1))
            # print()

            assert(x % 2 ** i == 1)
            # ==> 
            assert(x % 2 ** (i + 1) == 1)
        else:
            assert(x % 2 ** i == 1)
            # ==>
            assert((x + w28 * 2 ** i) % 2 ** (i + 1) == 1)


        w29 = w29 | w1
        w0 = w0 * 2
        assert((w29 * w28) % w0 == 1)

    assert((w29 * w28) % BASE == 1)

d0inv(2109612375)

from z3 import *

# w1 = BitVec("w1", num_bits)
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

# i = BitVecVal(30, 32)
# print(simplify(1 << (i + 1)))
x = BitVecVal(2147483649, 32)
print(simplify(x % 2147483648))
