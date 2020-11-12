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

# w16, 92952752686140917874786203514121980818059560611349214113624235610630918300666
# w17, 8757693327747761311693260668061283489019328934175151382091068302370316026475
# w18, 54078374504571553778978498794409297105293230067052244726208759455855310802617

machine.set_reg(16, 92952752686140917874786203514121980818059560611349214113624235610630918300666)
machine.set_reg(17, 8757693327747761311693260668061283489019328934175151382091068302370316026475)
machine.set_reg(18, 54078374504571553778978498794409297105293230067052244726208759455855310802617)

while cont:
    # log_str = 'imem: ' + str(machine.get_pc()) + ', #ins: ' + str(inst_cnt)
    cont, trace_str, cycles = machine.step()
    print(trace_str)
    inst_cnt += 1
    cycle_cnt += cycles