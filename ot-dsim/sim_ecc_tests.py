# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Runs ECC operations based on p256 firmware.

Runs ECC operations based on the primitives contained in the binary blob of
the p256 lib.
"""

from bignum_lib.machine import Machine
from bignum_lib.sim_helpers import *
from sim import ins_objects_from_hex_file
from sim import ins_objects_from_asm_file
from Crypto.Math.Numbers import Integer
from Crypto.PublicKey import ECC
from Crypto.Hash import SHA256
from Crypto.Signature import DSS
import sys

# Switch to True to get a full instruction trace
ENABLE_TRACE_DUMP = False

# Configuration for the statistics prints
STATS_CONFIG = {
    'instruction_histo_sort_by': 'key',
}

BN_WORD_LEN = 256
BN_LIMB_LEN = 32
BN_MASK = 2**BN_WORD_LEN-1
BN_LIMB_MASK = 2**BN_LIMB_LEN-1
#BN_MAX_WORDS = 16  # Max number of bn words per val (for 4096 bit words)
DMEM_DEPTH = 1024
PROGRAM_HEX_FILE = 'hex/dcrypto_p256.hex'
PROGRAM_ASM_FILE = 'asm/dcrypto_p256.asm_anno'
PROGRAM_OTBN_ASM_FILE = 'asm/dcrypto_p256.otbn_asm'

# pointers to dmem areas according to calling conventions of the p256 lib
pLoc = 0  # Location of pointer in dmem
pK = 1
pRnd = 2
pMsg = 3
pR = 4
pS = 5
pX = 6
pY = 7
pD = 8

P256INIT_START_ADDR = 22
P256INIT_STOP_ADDR = 43

P256ISONCURVE_START_ADDR = 82
P256ISONCURVE_STOP_ADDR = 105

P256SCALARMULT_START_ADDR = 618
P256SCALARMULT_STOP_ADDR = 629

P256SIGN_START_ADDR = 446
P256SIGN_STOP_ADDR = 479

P256VERIFY_START_ADDR = 538
P256VERIFY_STOP_ADDR = 617

P256_CURVE_ORDER = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

# Example key
# public
x = 0xb5511a6afacdc5461628ce58db6c8bf36ec0c0b2f36b06899773b7b3bfa8c334
y = 0x42a1c6971f31c14343dd09eab53a17fa7f7a11d0ab9c6924a87070589e008c2e
# private
d = 0xc0fbe2569144233de5f2cbee543b963b2d869bf4aa847f52fbd94efec7df1a56

# Example point on curve
xexp = 0xb5511a6afacdc5461628ce58db6c8bf36ec0c0b2f36b06899773b7b3bfa8c334
yexp = 0x42a1c6971f31c14343dd09eab53a17fa7f7a11d0ab9c6924a87070589e008c2e

# Example scalar
kexp = 0x1420fc41742102631b76ebe83fdfa3799590ef5db0b2c78121d0a016fe6d1071

# Example signature (for msg_digest and kexp)
rexp = 0x815215ad7dd27f336b35843cbe064de299504edd0c7d87dd1147ea5680a9674a
sexp = 0xa3991e01c444042086e30cd999e589ad4dad9404e90a6d17d0b1051ec93fd605

msg_str = b'Hello bignum, can you sign this for me?'
msg_digest = SHA256.new(msg_str)
msg_digest_int = int(msg_digest.hexdigest(), 16)

ins_objects = []
dmem = []
inst_cnt = 0
cycle_cnt = 0
stats = init_stats()

# Helper functions
def bit_len(int_type):
    """Helper function returning the number of bits required to binary encode an integer."""
    length = 0
    while int_type:
        int_type >>= 1
        length += 1
    return length


def test_bit(int_type, offset):
    """Helper function indicationg if a specific bit in the bin representation of an int is set."""
    mask = 1 << offset
    return bool(int_type & mask)


def egcd(a, b):
    """Helper function to run the extended euclidian algorithm"""
    if a == 0:
        return b, 0, 1
    g, y, x = egcd(b % a, a)
    return g, x - (b // a) * y, y


def mod_inv(val, mod):
    """Helper function to compute a modular inverse"""
    g, x, _ = egcd(val, mod)
    if g != 1:
        raise Exception('modular inverse does not exist')
    return x % mod


def get_msg_val(msg):
    """Helper function to return a ascii encoded bignum value for a string"""
    msg_hex_str = ''.join(format(ord(x), '02x') for x in msg)
    msg_val = int(msg_hex_str, 16)
    return msg_val


def get_msg_str(val):
    """Helper function to return a string for an ascii bignum value"""
    hex_str = hex(val)
    ret = ''
    for i in range(2, len(hex_str), 2):
        ret += chr(int(hex_str[i:i+2], 16))
    return ret


# DMEM manipulation
def init_dmem():
    global dmem
    """Create the simulator side of dmem and init with zeros."""
    dmem = [0]*DMEM_DEPTH


def load_pointer():
    """Load pointers into 1st dmem word according to calling conventions"""
    pval = pK
    pval += (pRnd << BN_LIMB_LEN*1)
    pval += (pMsg << BN_LIMB_LEN*2)
    pval += (pR << BN_LIMB_LEN*3)
    pval += (pS << BN_LIMB_LEN*4)
    pval += (pX << BN_LIMB_LEN*5)
    pval += (pY << BN_LIMB_LEN*6)
    pval += (pD << BN_LIMB_LEN*7)
    dmem[pLoc] = pval


def load_k(k):
    """Load the ECDSA nonce in dmem at appropriate location according to calling conventions"""
    dmem[pK] = k


def load_rnd(rnd):
    """Load the random seed in dmem at appropriate location according to calling conventions"""
    dmem[pRnd] = rnd


def load_msg(msg):
    """Load the msg digest in dmem at appropriate location according to calling conventions"""
    dmem[pMsg] = msg


def load_r(r):
    """Load the r value of the signature in dmem at appropriate location according to calling conventions"""
    dmem[pR] = r


def load_s(s):
    """Load the s value of the signature in dmem at appropriate location according to calling conventions"""
    dmem[pS] = s


def load_x(x):
    """Load the x coordinate of public key in dmem at appropriate location according to calling conventions"""
    dmem[pX] = x


def load_y(y):
    """Load the y coordinate of public key in dmem at appropriate location according to calling conventions"""
    dmem[pY] = y


def load_d(d):
    """Load the private key in dmem at appropriate location according to calling conventions"""
    dmem[pD] = d


# Program loading
def load_program_hex():
    """Load binary executable from file"""
    global ins_objects
    global ctx
    global start_addr_dict
    global stop_addr_dict
    global breakpoints

    breakpoints = {}

    insfile = open(PROGRAM_HEX_FILE)
    ins_objects, ctx = ins_objects_from_hex_file(insfile)
    insfile.close()

    start_addr_dict = {'p256init': P256INIT_START_ADDR, 'p256isoncurve': P256ISONCURVE_START_ADDR,
                       'p256scalarmult': P256SCALARMULT_START_ADDR, 'p256sign': P256SIGN_START_ADDR,
                       'p256verify': P256VERIFY_START_ADDR}
    stop_addr_dict = {'p256init': P256INIT_STOP_ADDR, 'p256isoncurve': P256ISONCURVE_STOP_ADDR,
                       'p256scalarmult': P256SCALARMULT_STOP_ADDR, 'p256sign': P256SIGN_STOP_ADDR,
                       'p256verify': P256VERIFY_STOP_ADDR}



def load_program_asm():
    """Load program from assembly file"""
    global ins_objects
    global ctx
    global start_addr_dict
    global stop_addr_dict
    global breakpoints

    insfile = open(PROGRAM_ASM_FILE)
    ins_objects, ctx, breakpoints = ins_objects_from_asm_file(insfile)
    insfile.close()

    # reverse function address dictionary
    function_addr = {v: k for k, v in ctx.functions.items()}
    start_addr_dict = {'p256init': function_addr['p256init'], 'p256isoncurve': function_addr['p256isoncurve'],
                       'p256scalarmult': function_addr['p256scalarmult'], 'p256sign': function_addr['p256sign'],
                       'p256verify': function_addr['p256verify']}
    stop_addr_dict = {'p256init': function_addr['MulMod']-1, 'p256isoncurve': function_addr['ProjAdd']-1,
                       'p256scalarmult': len(ins_objects)-1, 'p256sign': function_addr['p256scalarbasemult']-1,
                       'p256verify': function_addr['p256scalarmult']-1}


def load_program_otbn_asm():
    """Load program from otbn assembly file"""
    global ins_objects
    global ctx
    global start_addr_dict
    global stop_addr_dict
    global breakpoints

    insfile = open(PROGRAM_OTBN_ASM_FILE)
    ins_objects, ctx, breakpoints = ins_objects_from_asm_file(insfile)
    insfile.close()

    # reverse label address dictionary for function addresses (OTBN asm does not differantiate between generic
    # und function labels)
    function_addr = {v: k for k, v in ctx.labels.items()}
    start_addr_dict = {'p256init': function_addr['p256init'], 'p256isoncurve': function_addr['p256isoncurve'],
                       'p256scalarmult': function_addr['p256scalarmult'], 'p256sign': function_addr['p256sign'],
                       'p256verify': function_addr['p256verify']}
    stop_addr_dict = {'p256init': function_addr['MulMod']-1, 'p256isoncurve': function_addr['ProjAdd']-1,
                       'p256scalarmult': len(ins_objects)-1, 'p256sign': function_addr['p256scalarbasemult']-1,
                       'p256verify': function_addr['p256scalarmult']-1}


def dump_trace_str(trace_string):
    if ENABLE_TRACE_DUMP:
        print(trace_string)


def run_isoncurve(x, y):
    """Runs the isoncurve primitive to check if a point is a valid curve point"""
    global dmem
    global inst_cnt
    global cycle_cnt
    global ctx
    global stats
    load_pointer()
    machine = Machine(dmem.copy(), ins_objects, start_addr_dict['p256init'], stop_addr_dict['p256init'], ctx=ctx, breakpoints=breakpoints)
    cont = True
    while cont:
        cont, trace_str, cycles = machine.step()
        dump_trace_str(trace_str)
        inst_cnt += 1
        cycle_cnt += cycles
    dmem = machine.dmem.copy()
    load_x(x)
    load_y(y)
    machine.dmem = dmem.copy()
    machine.pc = start_addr_dict['p256isoncurve']
    machine.stop_addr = stop_addr_dict['p256isoncurve']
    cont = True
    machine.stats = stats
    while cont:
        cont, trace_str, cycles = machine.step()
        dump_trace_str(trace_str)
        inst_cnt += 1
        cycle_cnt += cycles
    dmem = machine.dmem.copy()
    # point is on curve if r and s are equal
    on_curve = (dmem[pS] == dmem[pR])
    return on_curve


def run_scalarmult(x, y, k):
    """Runs the scalarmult primitive to multiply a curve point with a scalar"""
    global dmem
    global inst_cnt
    global cycle_cnt
    global ctx
    global stats
    global breakpoints
    load_pointer()
    machine = Machine(dmem.copy(), ins_objects, start_addr_dict['p256init'], stop_addr_dict['p256init'], ctx=ctx, breakpoints=breakpoints)
    machine.stats = stats
    cont = True
    while cont:
        cont, trace_str, cycles = machine.step()
        dump_trace_str(trace_str)
        inst_cnt += 1
        cycle_cnt += cycles
    dmem = machine.dmem.copy()
    load_x(x)
    load_y(y)
    load_k(k)
    machine.dmem = dmem.copy()
    machine.pc = start_addr_dict['p256scalarmult']
    machine.stop_addr = stop_addr_dict['p256scalarmult']
    machine.stats = stats
    cont = True
    while cont:
        cont, trace_str, cycles = machine.step()
        dump_trace_str(trace_str)
        inst_cnt += 1
        cycle_cnt += cycles
    dmem = machine.dmem.copy()
    return dmem[pX], dmem[pY]


def run_sign(d, k, msg):
    """Runs the sign primitive to perform an ecdsa sign"""
    global dmem
    global inst_cnt
    global cycle_cnt
    global ctx
    global stats
    global breakpoints
    load_pointer()
    machine = Machine(dmem.copy(), ins_objects, start_addr_dict['p256init'], stop_addr_dict['p256init'], ctx=ctx, breakpoints=breakpoints)
    cont = True
    while cont:
        cont, trace_str, cycles = machine.step()
        dump_trace_str(trace_str)
        inst_cnt += 1
        cycle_cnt += cycles
    dmem = machine.dmem.copy()
    load_msg(msg)
    load_d(d)
    load_k(k)
    machine.dmem = dmem.copy()
    machine.pc = start_addr_dict['p256sign']
    machine.stop_addr = stop_addr_dict['p256sign']
    machine.stats = stats
    cont = True
    while cont:
        cont, trace_str, cycles = machine.step()
        dump_trace_str(trace_str)
        inst_cnt += 1
        cycle_cnt += cycles
    dmem = machine.dmem.copy()
    return dmem[pR], dmem[pS]


def run_verify(x, y, r, s, msg):
    """Runs the sign primitive to perform an ecdsa sign"""
    global dmem
    global inst_cnt
    global cycle_cnt
    global ctx
    global stats
    global breakpoints
    load_pointer()
    machine = Machine(dmem.copy(), ins_objects, start_addr_dict['p256init'], stop_addr_dict['p256init'], ctx=ctx, breakpoints=breakpoints)
    machine.stats = stats
    cont = True
    while cont:
        cont, trace_str, cycles = machine.step()
        dump_trace_str(trace_str)
        inst_cnt += 1
        cycle_cnt += cycles
    dmem = machine.dmem.copy()
    load_x(x)
    load_y(y)
    load_r(r)
    load_s(s)
    load_msg(msg)
    machine.dmem = dmem.copy()
    machine.pc = start_addr_dict['p256verify']
    machine.stop_addr = stop_addr_dict['p256verify']
    machine.stats = stats
    cont = True
    while cont:
        cont, trace_str, cycles = machine.step()
        dump_trace_str(trace_str)
        inst_cnt += 1
        cycle_cnt += cycles
    dmem = machine.dmem.copy()
    # Verification successful if r == rnd
    return dmem[pR] == dmem[pRnd]

def run_test_curvepoint_deterministic():
    res = run_isoncurve(xexp, yexp)
    if not res:
        raise Exception('Test point (deterministic) should be on curve')

def run_test_curvepoint_random():
    #rand = Integer.random_range(min_inclusive=1, max_exclusive=P256_CURVE_ORDER)
    randkey = ECC.generate(curve='P-256')
    randx = int(randkey.public_key().pointQ.x.to_bytes(32).hex(), 16)
    randy = int(randkey.public_key().pointQ.y.to_bytes(32).hex(), 16)

    res = run_isoncurve(randx, randy)
    if not res:
        raise Exception('Test point (random) should be on curve')

def run_test_scalarmul_deterministic():
    pointexp = ECC.EccPoint(xexp, yexp, curve='p256')
    resref = pointexp*kexp
    init_dmem()
    xres, yres = run_scalarmult(xexp, yexp, kexp)
    resbn = ECC.EccPoint(xres, yres, curve='p256')
    if not resref == resbn:
        raise Exception('Wrong result for scalar point multiplication (deterministic)')

def run_test_scalarmul_random():
    randkey = ECC.generate(curve='P-256')
    randx = int(randkey.public_key().pointQ.x.to_bytes(32).hex(), 16)
    randy = int(randkey.public_key().pointQ.y.to_bytes(32).hex(), 16)
    randk = int(Integer.random_range(min_inclusive=1, max_exclusive=P256_CURVE_ORDER).to_bytes(32).hex(), 16)
    randp = ECC.EccPoint(randx, randy, curve='p256')
    resref = randp*randk
    init_dmem()
    xres, yres = run_scalarmult(randx,randy, randk)
    resbn = ECC.EccPoint(xres, yres, curve='p256')
    if not resref == resbn:
        raise Exception('Wrong result for scalar point multiplication (random)')

def run_test_ecdsa_sign_deterministic():
    init_dmem()
    rres, sres = run_sign(d, kexp, msg_digest_int)
    rresb = rres.to_bytes(32, byteorder='big', signed=False)
    sresb = sres.to_bytes(32, byteorder='big', signed=False)
    rsresb = b''.join([rresb, sresb])
    verkey = ECC.construct(curve='p256', point_x=x, point_y=y, d=d)
    verifier = DSS.new(verkey, 'fips-186-3')
    try:
        verifier.verify(msg_digest, rsresb)
    except ValueError:
        raise Exception('ECDSA sign (deterministic) failed')

def run_test_ecdsa_sign_random():
    init_dmem()
    randkey = ECC.generate(curve='P-256')
    randd = int(randkey.d.to_bytes(32).hex(), 16)
    randk = int(Integer.random_range(min_inclusive=1, max_exclusive=P256_CURVE_ORDER).to_bytes(32).hex(), 16)
    rres, sres = run_sign(randd, randk, msg_digest_int)
    rresb = rres.to_bytes(32, byteorder='big', signed=False)
    sresb = sres.to_bytes(32, byteorder='big', signed=False)
    rsresb = b''.join([rresb, sresb])
    verifier = DSS.new(randkey, 'fips-186-3')
    try:
        verifier.verify(msg_digest, rsresb)
    except ValueError:
        raise Exception('ECDSA sign (random) failed')

def run_test_ecdsa_verify_deterministic():
    init_dmem()
    res = run_verify(xexp, yexp, rexp, sexp, msg_digest_int)
    if not res:
        raise Exception('ECDSA verifiy (deterministic) failed')

def run_test_ecdsa_verify_random():
    init_dmem()
    randkey = ECC.generate(curve='P-256')
    randx = int(randkey.public_key().pointQ.x.to_bytes(32).hex(), 16)
    randy = int(randkey.public_key().pointQ.y.to_bytes(32).hex(), 16)
    signer = DSS.new(randkey, 'fips-186-3')
    signature = signer.sign(msg_digest)
    r = int.from_bytes(signature[0:32], byteorder='big', signed=False)
    s = int.from_bytes(signature[32:64], byteorder='big', signed=False)
    res = run_verify(randx, randy, r, s, msg_digest_int)
    if not res:
        raise Exception('ECDSA verifiy (rand) failed')

def run_test(name):
    global inst_cnt
    global cycle_cnt
    global ctx
    global stats

    test_results = {
        'inst_cnt': 0,
        'cycle_cnt': 0,
        'stats': {},
    }

    # reset global counter variables
    inst_cnt = 0
    cycle_cnt = 0
    stats = init_stats()

    # run test
    getattr(sys.modules[__name__], "run_test_" + name)()

    # append test results
    test_results['inst_cnt'] = inst_cnt
    test_results['cycle_cnt'] = cycle_cnt
    test_results['stats'] = stats

    dump_stats(stats, STATS_CONFIG)
    print("Total: %d instructions, taking %d cycles." % (inst_cnt, cycle_cnt))

    return test_results


def main():
    """main"""
    global inst_cnt
    global cycle_cnt
    global ctx
    global stats
    global start_addr_dict
    global stop_addr_dict
    global breakpoints

    init_dmem()

    inst_cnt = 0
    cycle_cnt = 0

    # select program source
    load_program_hex()
    #load_program_asm()
    #load_program_otbn_asm()

    # curve point test (deterministic)
    print_test_headline(1, 8, "curve point test (deterministic)")
    run_test("curvepoint_deterministic")

    # curve point test (random)
    print_test_headline(2, 8, "curve point test (random)")
    run_test("curvepoint_random")

    # scalar multiplication (deterministic)
    print_test_headline(3, 8, "scalar multiplication (deterministic)")
    run_test("scalarmul_deterministic")

    # scalar multiplication (random)
    print_test_headline(4, 5, "scalar multiplication (random)")
    run_test("scalarmul_random")

    # ECDSA sign (deterministic)
    print_test_headline(5, 8, "ECDSA sign (deterministic)")
    run_test("ecdsa_sign_deterministic")

    # ECDSA sign (random (random key, random k, deterministic message digest))
    print_test_headline(6, 8, "ECDSA sign (random (random key, random k, deterministic message digest))")
    run_test("ecdsa_sign_random")

    # ECDSA verify (deterministic)
    print_test_headline(7, 8, "ECDSA verify (deterministic)")
    run_test("ecdsa_verify_deterministic")

    # ECDSA verify (random)
    print_test_headline(8, 8, "ECDSA verify (random)")
    run_test("ecdsa_verify_random")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("Cancelled by user request.")
