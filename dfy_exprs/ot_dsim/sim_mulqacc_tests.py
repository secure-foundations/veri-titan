# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Runs a multiplication (512=256x256 bit) based on a sequence of MULQACC instructions

Uses two random 256 bit wide operands and checks the result for corectness
"""

from bignum_lib.machine import Machine
from bignum_lib.sim_helpers import *
import random

# Switch to True to get a full instruction trace
ENABLE_TRACE_DUMP = True

BN_WORD_LEN = 256
BN_MASK = 2**BN_WORD_LEN-1
BN_MAX_WORDS = 16  # Max number of bn words per val (for 4096 bit words)
DMEM_DEPTH = 1024
PROGRAM_ASM_FILE = 'asm/otbn_mulqacc_256x256.asm'

ins_objects = []
dmem = []

def init_dmem():
    global dmem
    """Create the simulator side of dmem and init with zeros."""
    dmem = [0]*DMEM_DEPTH

def load_program_asm():
    """Load program from assembly file"""
    global ins_objects
    global ctx
    global breakpoints

    insfile = open(PROGRAM_ASM_FILE)
    ins_objects, ctx, breakpoints = ins_objects_from_asm_file(insfile)
    insfile.close()

def dump_trace_str(trace_string):
    if ENABLE_TRACE_DUMP:
        print(trace_string)

def run_mult(op1, op2):
    global dmem
    global ctx
    dmem[0] = op1
    dmem[1] = op2
    machine = Machine(dmem.copy(), ins_objects, 0, 23, ctx=ctx, breakpoints=breakpoints)
    cont = True
    while cont:
        cont, trace_str, cycles = machine.step()
        dump_trace_str(trace_str)
    dmem = machine.dmem.copy()
    res_low = dmem[2]
    res_high = dmem[3]
    res = (res_high << 256) + res_low
    return res


def main():
    """main"""
    global stats
    global ctx
    init_dmem()

    load_program_asm()

    random.seed()
    op1 = random.getrandbits(256)
    op2 = random.getrandbits(256)

    res = run_mult(op1, op2)

    print('Operand 1: ')
    print(hex(op1))
    print('Operand 2: ')
    print(hex(op2))
    print ('Result from simulator: ')
    print(hex(res))
    print ('Golden result: ')
    print(hex(op1*op2))

    if res != op1*op2:
        raise Exception("Wrong result")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("Cancelled by user request.")
