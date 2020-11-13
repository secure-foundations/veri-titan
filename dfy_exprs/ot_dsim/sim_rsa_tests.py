# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Runs RSA operations based on bignum binary.

Runs RSA operations based on the primitives contained in the binary blob of
the generic bignum library. Hence these are wrappers around mainly modexp and
montmul operations.
"""

from bignum_lib.machine import Machine
from bignum_lib.sim_helpers import *

# Switch to True to get a full instruction trace
ENABLE_TRACE_DUMP = False

# Configuration for the statistics prints
STATS_CONFIG = {
    'instruction_histo_sort_by': 'key',
}
DMEM_BYTE_ADDRESSING=True

BN_WORD_LEN = 256
BN_LIMB_LEN = 32
BN_MASK = 2**BN_WORD_LEN-1
BN_LIMB_MASK = 2**BN_LIMB_LEN-1
BN_MAX_WORDS = 16  # Max number of bn words per val (for 4096 bit words)
DMEM_DEPTH = 1024
PROGRAM_HEX_FILE = 'hex/dcrypto_bn.hex'
PROGRAM_ASM_FILE = 'asm/dcrypto_bn.asm'
PROGRAM_OTBN_ASM_FILE = 'asm/modexp.S'

# pointers to dmem areas according to calling conventions for bignum lib
dmem_mult = 32 if DMEM_BYTE_ADDRESSING else 1
DMEMP_IN = 38*dmem_mult
DMEMP_MOD = 4*dmem_mult
DMEMP_RR = 22*dmem_mult
DMEMP_EXP = 54*dmem_mult
DMEMP_OUT = 71*dmem_mult
DMEMP_DINV = 20*dmem_mult
DMEMP_BLINDING = 21*dmem_mult
DMEMP_BIN = 87*dmem_mult
DMEMP_BOUT = 103*dmem_mult

DMEM_LOC_IN_PTRS = 0
DMEM_LOC_SQR_PTRS = 1
DMEM_LOC_MUL_PTRS = 2
DMEM_LOC_OUT_PTRS = 3

# RSA private keys
RSA_D = {}
# noinspection LongLine
RSA_D[768] = 0xaeadb950258c1b5c9f42d33e7675df4546ab5ba6ceb972494e66c82431a7f961db12f2c132117b9023b0b9453f065da2d7350fddfc03df8d916b83f959ee671e1a209e8bf8f6e2b2f529714c2254cf7e97bc7024dd6d52fe17d9d6417b764001  # pylint: disable=line-too-long
# noinspection LongLine
RSA_D[1024] = 0x9a6d85f407a86d619a2f837bc8e3fb7cbdb5792e4826b7929c956ff5677698063bea9e7a106312136a4480869a95566fe0ba578c7ed4f87d95b8b1c9f88cc66ee57ba0afa04e4e84d797b95add32e52be580b3b2bf56ff01dce6a66c4a811d8fea4bed2408f467af0df2fd373f3125faee35b0db6611ff49e1e5ff1bccc30e09  # pylint: disable=line-too-long
# noinspection LongLine
RSA_D[2048] = 0x4e9d021fdf4a8b89bc8f14e26f15665a6770197fb9435668fbaaf326dbaddf6e7cb4a3d026bef3a3dc8fdf74f0895eca86312c3380ea291939ad329f142095c0401ba3a491f7eac1351687960a7696026ba2c0d38dc6324eaf8baedc4247c1856e5e94f252fa27e7222494eb67be1ee48291de710ab8231a02e7cc8206d22615549752cdf53f6dc6b97030bec588a6b065169c4c84e27a6ee9c7bdcf4527fc19c6231d2b88a2671fc2d6d3a079fbbfea38a8df4fbc9b8eee04b77c00d7951a03827ae841b8b1af7ff13089566d07115579dd680f82085ccc2447546886f1f03f5210ade4163316022162e32f5deb225b64b42922742429a94c668431ca9995f5  # pylint: disable=line-too-long
# noinspection LongLine
RSA_D[3072] = 0x19708fcd3b552cb65238e843e38c30505682d206c163739bf3429c22068c3bcaab23d96fefee6f3341839f98e5dae2c04f5410aeeb76bb423e89a8c5dd721721bf1f9c1070d3a4c9b5bf7f6966c89836f4bea8d8c157dd0bd8462eeb19eddd5c72b507b46c6c44bd91d6ba2a005ee2e50f08f1c2498f9d3a953519023b98f3853e5a51c65f7b37bd9576439af98eb985d8caeffb5d44438e0d93fe61676a014275989f33b8f8398394da637be37d8576af488d2acaf141c33eb18cf76be91400af9684c249b9a7fed7a28a52bd11dceb0a8453538b4cb84da9c991507fdf71ff083441dd7bf7a488a25a3599a4943dd919f302a9b7442b6bcc835946ba9457ff25f4ea6176ee00ade999fad40468f8de12fec788a836c1f777b8f1f7359a32cfd92629f9f49b7360f688aa12f94769d57fc82f1feabecb5adcd454c4552b2c628dfd2626d1abe943855330f65711537176cad2996ce98e717023ac653061587cc8f26c859d9ac19ac762fbaf6f2de8ffab23a35c94265fe08a082ba7b4e44c1

# RSA modulus
RSA_N = {}
# noinspection LongLine
RSA_N[768] = 0xb0dbed46d932f07cd42023d2355a8617db247236333bc2648ba4496e74fefad2820cc4123a4867e115cc94df441b4ec018ba461b512ce20fc03277ed5f8be5a300e63c2da7108953a82b337438f73600fddd5bbd7bc17ce175902b782d398569  # pylint: disable=line-too-long
# noinspection LongLine
RSA_N[1024] = 0xdf4eaf7345949834307e26ad4083f91721b04e1b0d6a44ce4e3e2e724c97df898a391025ae204cf23b20b2a510ddb26b624ea69f924ad98697cc70203b6a3263ca7f59fb57b6a999e9d02e0f1cd47d8ba0bd0fd2d53b1f11b46a94cf4f0a2b44e7fa6b2491b4821ff675b691c5a0f62fd5ff10739b34f67a8823a9423ca82491  # pylint: disable=line-too-long
# noinspection LongLine
RSA_N[2048] = 0x9cd7612e438e15becd739fb7f5864be395905c85194c1d2e2cef6e1fed75320f0ac1729f0c7850a299825390be642349757b0ceb2d6897d6afb1aa2ade5e9be3060df2acd9d71f506ec95debb4f0c0982304304610dcd46b57c730c306ddaf516e4041f810de491852b318ca4950a83acdb6947bdbf12d05ce570bbe3848bbc9b17636b8a8cce2075cc87bcfcff0faa3c5d73a5eb2f4bfeac2ed5116a2929c36a6860e24a56615e797225004ffc94db0bc27055e2cf7efdc5d58a13b6083b78cb7d0366d552e052363744a9737a77840ef3e66fdba6eb3724a21821f33ad620cf21ad26ab5a7f251691f38a5579ac58867e311a6534fb1e90741dee8df93a999  # pylint: disable=line-too-long
# noinspection LongLine
RSA_N[3072] = 0xda7b57497c76318a1b0e4eb6dc59584918fded8d11e48869db8471c8fba5c5fc4388602c7dad25d74fd55314988ca03f5bb0233bb5fcb6538eeeb1e9144e46a3900289e2042bbb0b37fc3026b10cccbb9dbbfec4c30eed248c39f35f55ca95d3075621f42ef7072d80de32597048f21869f77898057aeaca5fa54b21a93de8a5c1fb5e60dea0cc1db872a217d09a58f21f3d4e3c76a8cbee5b8b7c6a683024c1402a13a3c5f175f63c1d15e8958cd10965e06c7cf21f8edcee55861da81e7220842e168cb1180c95af0df9cda50818e5519b50cdacf23a1d63571245975dbec04fa511278f069cc0d3d8e471241bf13939c9d0034860b536d29a3162d9ec5d684ac20ead2cd4f46c49522323a8d3650d63796a76b6b07b4b7bdd98922b7af54f5c67e51aaf5d84d4a2a3a104c0fa7f343f468f27f93c74fce64f86bee7ca6de90a2f3cb2d696e68c9c044fef54d54f3a15cedb2e8b54f90f3b3426cab25c9f8f08ac0496b5026f8b2f6470837da95855ddf20215e6010f3e48caa441ee813625

# RSA public exponent
EXP_PUB = 65537

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


def load_pointer(bn_words, p_loc, p_a, p_b, p_c):
    """Load pointers into 1st dmem word according to calling conventions"""
    pval = DMEMP_MOD
    pval += (DMEMP_DINV << BN_LIMB_LEN*1)
    pval += (DMEMP_RR << BN_LIMB_LEN*2)
    pval += (p_a << BN_LIMB_LEN*3)
    pval += (p_b << BN_LIMB_LEN*4)
    pval += (p_c << BN_LIMB_LEN*5)
    pval += (bn_words << BN_LIMB_LEN*6)
    pval += ((bn_words-1) << BN_LIMB_LEN*7)
    dmem[p_loc] = pval


def load_blinding(pubexp, rnd, pad1, pad2):
    """Load pointers into 1st dmem word according to calling conventions"""
    bval = pubexp
    bval += ((pad1 & BN_LIMB_MASK) << BN_LIMB_LEN*1)
    bval += (((pad1 >> BN_LIMB_LEN) & BN_LIMB_MASK) << BN_LIMB_LEN*2)
    bval += (((pad1 >> BN_LIMB_LEN*2) & BN_LIMB_MASK) << BN_LIMB_LEN*3)
    bval += ((rnd & BN_LIMB_MASK) << BN_LIMB_LEN*4)
    bval += (((rnd >> BN_LIMB_LEN) & BN_LIMB_MASK) << BN_LIMB_LEN*5)
    bval += ((pad2 & BN_LIMB_MASK) << BN_LIMB_LEN*6)
    bval += (((pad2 >> BN_LIMB_LEN) & BN_LIMB_MASK) << BN_LIMB_LEN*7)
    dmem[DMEMP_BLINDING] = bval


def load_full_bn_val(dmem_p, bn_val):
    """Load a full multi-word bignum value into dmem"""
    for i in range(0, BN_MAX_WORDS):
        dmem[dmem_p//dmem_mult+i] = (bn_val >> (BN_WORD_LEN*i)) & BN_MASK


def get_full_bn_val(dmem_p, machine, bn_words=BN_MAX_WORDS):
    """Get a full multi-word bignum value form dmem"""
    bn_val = 0
    for i in range(0, bn_words):
        bn_val += machine.get_dmem(i+dmem_p//dmem_mult) << (BN_WORD_LEN*i)
    return bn_val


def load_mod(mod):
    """Load the modulus in dmem at appropriate location according to calling conventions"""
    load_full_bn_val(DMEMP_MOD, mod)


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

    start_addr_dict = {'modload': 414, 'mulx': 172, 'mul1': 236, 'modexp': 303, 'modexp_blinded': 338}
    stop_addr_dict = {'modload': 425, 'mulx': 190, 'mul1': 239, 'modexp': 337,  'modexp_blinded': 413}


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
    start_addr_dict = {'modload': function_addr['modload'], 'mulx': function_addr['mulx'],
                       'mul1': function_addr['mul1'], 'modexp': function_addr['modexp'],
                       'modexp_blinded': function_addr['modexp_blinded'] }
    stop_addr_dict = {'modload': function_addr['selA0orC4']-1, 'mulx': function_addr['mm1_sub_cx']-1,
                       'mul1': function_addr['sqrx_exp']-1, 'modexp': function_addr['modexp_blinded']-1,
                       'modexp_blinded': function_addr['modload']-1}


def load_program_otbn_asm():
    """Load program from otbn assembly file"""
    global ins_objects
    global ctx
    global start_addr_dict
    global stop_addr_dict
    global breakpoints

    insfile = open(PROGRAM_OTBN_ASM_FILE)
    ins_objects, ctx, breakpoints = ins_objects_from_asm_file(insfile, dmem_byte_addressing=DMEM_BYTE_ADDRESSING, otbn_only=True)
    insfile.close()

    # reverse label address dictionary for function addresses (OTBN asm does not differentiate between generic
    # und function labels)
    function_addr = {v: k for k, v in ctx.labels.items()}
    start_addr_dict = {'modload': function_addr['modload'], 'mulx': function_addr['mulx'],
                       'mul1': function_addr['mul1'], 'modexp': function_addr['modexp'] }
    stop_addr_dict = {'modload': len(ins_objects)-1, 'mulx': function_addr['mm1_sub_cx']-1,
                       'mul1': function_addr['sqrx_exp']-1, 'modexp': function_addr['modload']-1}


def dump_trace_str(trace_string):
    if ENABLE_TRACE_DUMP:
        print(trace_string)


# primitive access
def run_modload(bn_words):
    """Runs the modload primitive (modload).

    Other than it's name suggests this primitive computes RR and the
    montgomery inverse dinv. The modulus is actually directly loaded into dmem
    beforehand. This primitive has to be executed every time, dmem was cleared.
    """
    global dmem
    global inst_cnt
    global cycle_cnt
    global stats
    global ctx

    load_pointer(bn_words, DMEM_LOC_IN_PTRS, DMEMP_IN, DMEMP_EXP, DMEMP_OUT)
    #breakpoints.append(start_addr_dict['modload'])
    machine = Machine(dmem.copy(), ins_objects, start_addr_dict['modload'], stop_addr_dict['modload'], ctx=ctx, breakpoints=breakpoints)
    machine.stats = stats
    cont = True
    while cont:
        cont, trace_str, cycles = machine.step()
        dump_trace_str(trace_str)
        inst_cnt += 1
        cycle_cnt += cycles
    dmem = machine.dmem.copy()
    dinv_res = dmem[DMEMP_DINV//dmem_mult]
    rr_res = get_full_bn_val(DMEMP_RR, machine, bn_words)
    return dinv_res, rr_res


def run_montmul(bn_words, p_a, p_b, p_out):
    """Runs the primitive for montgomery multiplication (mulx)"""
    global dmem
    global inst_cnt
    global cycle_cnt
    global stats
    global ctx
    global breakpoints
    load_pointer(bn_words, DMEM_LOC_IN_PTRS, p_a, p_b, p_out)
    machine = Machine(dmem.copy(), ins_objects, start_addr_dict['mulx'], stop_addr_dict['mulx'], ctx=ctx, breakpoints=breakpoints)
    machine.stats = stats
    cont = True
    i = 0
    while cont:
        cont, trace_str, cycles = machine.step()
        i += 1
        dump_trace_str(trace_str)
        inst_cnt += 1
        cycle_cnt += cycles
    res = get_full_bn_val(DMEMP_OUT, machine, bn_words)
    dmem = machine.dmem.copy()
    return res


def run_montout(bn_words, p_a, p_out):
    """Runs the primitive for back-transformation from the montgomery domain (mul1)"""
    global dmem
    global inst_cnt
    global cycle_cnt
    global stats
    global ctx
    load_pointer(bn_words, DMEM_LOC_IN_PTRS, p_a, 0, p_out)
    machine = Machine(dmem.copy(), ins_objects, start_addr_dict['mul1'], stop_addr_dict['mul1'], ctx=ctx)
    machine.stats = stats
    cont = True
    while cont:
        cont, trace_str, cycles = machine.step()
        dump_trace_str(trace_str)
        inst_cnt += 1
        cycle_cnt += cycles
    res = get_full_bn_val(DMEMP_OUT, machine, bn_words)
    dmem = machine.dmem.copy()
    return res


def run_modexp(bn_words, exp):
    """Runs the primitive for modular exponentiation (modexp)"""
    global dmem
    global inst_cnt
    global cycle_cnt
    global stats
    global ctx
    load_full_bn_val(DMEMP_EXP, exp)
    load_pointer(bn_words, DMEM_LOC_IN_PTRS, DMEMP_IN, DMEMP_RR, DMEMP_IN)
    load_pointer(bn_words, DMEM_LOC_SQR_PTRS, DMEMP_OUT, DMEMP_OUT, DMEMP_OUT)
    load_pointer(bn_words, DMEM_LOC_MUL_PTRS, DMEMP_IN, DMEMP_OUT, DMEMP_OUT)
    load_pointer(bn_words, DMEM_LOC_OUT_PTRS, DMEMP_OUT, DMEMP_EXP, DMEMP_OUT)
    machine = Machine(dmem.copy(), ins_objects, start_addr_dict['modexp'], stop_addr_dict['modexp'], ctx=ctx)
    machine.stats = stats
    cont = True
    while cont:
        cont, trace_str, cycles = machine.step()
        dump_trace_str(trace_str)
        inst_cnt += 1
        cycle_cnt += cycles
    res = get_full_bn_val(DMEMP_OUT, machine, bn_words)
    dmem = machine.dmem.copy()
    return res


def run_modexp_blinded(bn_words, exp):
    """Runs the primitive for modular exponentiation (modexp)"""
    global dmem
    global inst_cnt
    global cycle_cnt
    global stats
    global ctx
    load_full_bn_val(DMEMP_EXP, exp)
    load_pointer(bn_words, DMEM_LOC_IN_PTRS, DMEMP_IN, DMEMP_RR, DMEMP_IN)
    load_pointer(bn_words, DMEM_LOC_SQR_PTRS, DMEMP_OUT, DMEMP_OUT, DMEMP_OUT)
    load_pointer(bn_words, DMEM_LOC_MUL_PTRS, DMEMP_IN, DMEMP_OUT, DMEMP_OUT)
    load_pointer(bn_words, DMEM_LOC_OUT_PTRS, DMEMP_OUT, DMEMP_EXP, DMEMP_OUT)
    load_blinding(EXP_PUB,0,0,0)
    machine = Machine(dmem.copy(), ins_objects, start_addr_dict['modexp_blinded'], stop_addr_dict['modexp_blinded'],
                      ctx=ctx)
    machine.stats = stats
    cont = True
    while cont:
        cont, trace_str, cycles = machine.step()
        dump_trace_str(trace_str)
        inst_cnt += 1
        cycle_cnt += cycles
    res = get_full_bn_val(DMEMP_OUT, machine, bn_words)
    dmem = machine.dmem.copy()
    return res


# Primitive wrappers
def modexp_word(bn_words, inval, exp):
    """Performs a full modular exponentiation with word sized exponent using several primitives.

    Performs a full modular exponentiation with a "small" exponent fitting into a single bignum
    word.
    After calculating constants (RR and dinv) the primitive for montgomery multiplication is wrapped
    with a standard square-and-multiply algorithm.
    Finally performs back-transformation from montgomery domain with the mul1 primitive
    """
    load_full_bn_val(DMEMP_IN, inval)
    run_montmul(bn_words, DMEMP_IN, DMEMP_RR, DMEMP_OUT)
    run_montmul(bn_words, DMEMP_IN, DMEMP_RR, DMEMP_IN)
    exp_bits = bit_len(exp)
    for i in range(exp_bits-2, -1, -1):
        run_montmul(bn_words, DMEMP_OUT, DMEMP_OUT, DMEMP_OUT)
        if test_bit(exp, i):
            run_montmul(bn_words, DMEMP_IN, DMEMP_OUT, DMEMP_OUT)
    res = run_montout(bn_words, DMEMP_OUT, DMEMP_OUT)
    return res


# tests
# noinspection PyPep8Naming
def check_rr(mod, rr_test):
    """Check if RR calculated with simulator matches a locally computed one"""
    R = 1 << bit_len(mod)
    RR = R*R % mod
    assert rr_test == RR, "Mismatch of local and machine calculated RR"


def check_dinv(dinv_test, r_mod, mod):
    """Check if montgomery modular inverse from simulator matches a locally computed one"""
    mod_i = mod_inv(mod, r_mod)
    dinv = (-mod_i) % r_mod
    assert dinv_test == dinv, "Mismatch of local and machine calculated montgomery constant"


def check_modexp(modexp_test, inval, exp, mod):
    """Check if modular exponentiation result from simulator matches locally computed result"""
    modexp_cmp = (inval**exp) % mod
    assert modexp_test == modexp_cmp,\
        "Mismatch of local and machine calculated modular exponentiation result"


def check_decrypt(msg_test, msg):
    """Check if decrypted string matches the original one"""
    assert msg_test == msg, "Mismatch between original and decrypted message"


# RSA
def rsa_encrypt(mod, bn_words, msg):
    """RSA encrypt"""
    #init_dmem()
    load_mod(mod)
    dinv, rr = run_modload(bn_words)
    check_dinv(dinv, 2**BN_WORD_LEN, mod)
    check_rr(mod, rr)
    load_full_bn_val(DMEMP_IN, msg)
    enc = modexp_word(bn_words, msg, EXP_PUB)
    check_modexp(enc, msg, EXP_PUB, mod)
    return enc


def rsa_decrypt(mod, bn_words, priv_key, enc):
    """RSA decrypt"""
    init_dmem()
    load_mod(mod)
    run_modload(bn_words)
    load_full_bn_val(DMEMP_IN, enc)
    decrypt = run_modexp(bn_words, priv_key)
    #decrypt = run_modexp_blinded(bn_words, priv_key)
    return decrypt

def main():
    """main"""
    global inst_cnt
    global cycle_cnt
    global stats
    global ctx
    global start_addr_dict
    global stop_addr_dict
    global breakpoints
    init_dmem()

    # select program source
    #load_program_hex()
    #load_program_asm()
    load_program_otbn_asm()

    msg_str = 'Hello bignum, can you encrypt and decrypt this for me?'
    msg = get_msg_val(msg_str)

    tests = [
        ('enc', 768),
        ('dec', 768),
        ('enc', 1024),
        ('dec', 1024),
        ('enc', 2048),
        ('dec', 2048),
        ('enc', 3072),
        ('dec', 3072)
    ]
    tests_results = []

    for i in range(len(tests)):
        test = tests[i]
        test_op, test_width = test
        print_test_headline(i+1, len(tests), str(test))
        test_results = {
            'inst_cnt': 0,
            'cycle_cnt': 0,
            'stats': {},
        }
        # reset global counter variables
        inst_cnt = 0
        cycle_cnt = 0
        stats = init_stats()

        if test_op == 'enc':
            enc = rsa_encrypt(RSA_N[test_width], test_width // 256, msg)
            print('encrypted message: ' + hex(enc))
        elif test_op == 'dec':
            decrypt = rsa_decrypt(RSA_N[test_width], test_width // 256,
                                  RSA_D[test_width], enc)
            check_decrypt(msg, decrypt)
            print('decrypted message: ' + get_msg_str(decrypt))
        else:
            assert True

        test_results['inst_cnt'] = inst_cnt
        test_results['cycle_cnt'] = cycle_cnt
        test_results['stats'] = stats

        tests_results.append(test_results)

        dump_stats(stats, STATS_CONFIG)

        print('Cycle count: ' + str(cycle_cnt))
        print('Instruction count ' + str(inst_cnt))

        print("\n\n")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("Cancelled by user request.")
