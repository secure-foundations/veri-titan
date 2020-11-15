import sys
from ot_dsim.bignum_lib.instructions import *
from ot_dsim.bignum_lib.sim_helpers import ins_objects_from_asm_file

asm_file = open(sys.argv[1])
ins_objects, ins_ctx, _ = ins_objects_from_asm_file(asm_file, otbn_only=False)
asm_file.close()

class SSAVar:
    def __init__(self, original, minor):
        self.original = original
        self.minor = minor

    def __str__(self):
        return str(self.original) + "_" + str(self.minor)

class Converter:
    def __init__(self, inputs):
        self.ssa_vars = dict()
        for input in inputs:
            self.get_rd(input)

    def get_rd(self, r):
        if r not in self.ssa_vars:
            self.ssa_vars[r] = 0
        else:
            self.ssa_vars[r] += 1
        return SSAVar(r, self.ssa_vars[r])

    def get_rs(self, r):
        if r is None:
            return None
        return SSAVar(r, self.ssa_vars[r])

c = Converter([8, 9, 16, 17, 18, 24, 25, 31])

addr = ins_ctx.get_label_addr_from_name("barrett384")
# print(addr)

for ins in ins_objects[addr:]:
    print(ins.get_asm_str()[1])

print("")

for ins in ins_objects[addr:]:
    ins.convert(c)
    print(ins.get_asm_str()[1])
    # print("")

print("")

machine = Machine([], ins_objects, addr, None, ins_ctx)

# cont = True

# machine.set_reg((16, 0), 0xcd8164c3de1b71062e90b431439988a2cef26b707ce224ba84e1b431bf90e3fa)
# machine.set_reg((17, 0), 0x135cadc39237aa29ae0813517b58a83731875308a2cd045f1a6a4fb59a4d026b)
# machine.set_reg((18, 0), 0x778f467950ba8aecb6dd8f7b865757e7a510c901b9d50297727b7c284d640eb9)

# while cont:
#     cont, trace_str, cycles = machine.step()
#     if trace_str != "":
#         print(trace_str)
