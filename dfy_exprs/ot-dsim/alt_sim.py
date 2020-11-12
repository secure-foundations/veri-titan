import sys
from bignum_lib.instructions import *
from bignum_lib.sim_helpers import ins_objects_from_asm_file

asm_file = open(sys.argv[1])
ins_objects, ins_ctx, _ = ins_objects_from_asm_file(asm_file, otbn_only=False)
asm_file.close()

machine = Machine([], ins_objects, 0, None, ins_ctx)

cont = True
inst_cnt = 0
cycle_cnt = 0

machine.set_reg(16, 0xcd8164c3de1b71062e90b431439988a2cef26b707ce224ba84e1b431bf90e3fa)
machine.set_reg(17, 0x135cadc39237aa29ae0813517b58a83731875308a2cd045f1a6a4fb59a4d026b)
machine.set_reg(18, 0x778f467950ba8aecb6dd8f7b865757e7a510c901b9d50297727b7c284d640eb9)

while cont:
    # log_str = 'imem: ' + str(machine.get_pc()) + ', #ins: ' + str(inst_cnt)
    cont, trace_str, cycles = machine.step()
    print(trace_str)
    inst_cnt += 1
    cycle_cnt += cycles