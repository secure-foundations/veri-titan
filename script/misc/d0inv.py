import sys

num_bits = int(sys.argv[1])
BASE = 2 ** num_bits

def print_bin(num):
    print(bin(num)[2:][-num_bits:].zfill(num_bits))


def d0inv(w28):
    w0 = 2
    w29 = 1

    for i in range(1, num_bits):
        w1 = (w28 * w29) % BASE
        w29_ = w29

        w1 = w1 & w0
        w29 = w29 | w1
        w0 = w0 * 2

        assert(((w28 * w29_) % BASE) % (1 << i) == 1)

        # print_bin((w28 * w29_) % BASE)
        # print_bin((w28 * w29) % BASE)
        # print()
        # print_bin(1 << i)
        # print_bin(1 << (i + 1))

        if w1 == 0:
            assert (w29_ == w29)

            # ==> 
            # assert(x % (1 << (i + 1)) == 1)
        else:
            assert(w29 == w29_ + (1 << i))

            # print_bin(x)
            # print_bin(1 << i)
            # print_bin(1 << (i + 1))
            # print()

            # assert(x % (1 << i) == 1)
            # # ==>
            # assert((x + w28 * (1 << i)) % w0 == 1)

            # assert ((x + w28 * (1 << i)) % BASE == 
            # (w29 * w28) % BASE)

        assert((w29 * w28) % w0 == 1)

    assert((w29 * w28) % BASE == 1)

d0inv(2109612375)

from z3 import *

def export_to_smtlib(query, file_name):
    s = Solver()
    s.add(Not(query))
    print(s.sexpr())
    print("(check-sat)")

x = BitVec("x", num_bits)
i = BitVec("i", num_bits)

query = Implies(
    And(
        0 <= i,
        i < num_bits,
        x & ((1 << i) - 1) == 1,
        # URem(x, (1 << i)) == 1,
        x & (1 << i) == 0,
    ),
    x & ((1 << (i+1)) - 1)  == 1,
    # URem(x, (1 << (i + 1))) == 1,
)
prove(query)

# export_to_smtlib(query, "test1.smt2")

w28 = BitVec("w28", num_bits)

query = Implies(
    And(
        0 <= i,
        i < num_bits,
        x & ((1 << i) - 1) == 1,
        # URem(x, (1 << i)) == 1,
        x & (1 << i) == (1 << i),
        w28 & 1 == 1,
    ),
    (x + w28 * (1 << i)) & ((1 << (i+1)) - 1)  == 1,
    # URem(x + w28 * (1 << i), (1 << (i + 1))) == 1,
)
prove(query)
