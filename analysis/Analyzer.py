import sys, ast
from ValeParser import *
from DfyParser import DafnyParser
from ValeParser import *

target_name = "dw_add"

vale_ast = open("vale.ast").read()
vale_ast = ast.literal_eval(vale_ast)

vproc = ValeProc(vale_ast)
assert (vproc.name == target_name)

dparser = DafnyParser(target_name)
dproc = dparser.get_target_method()

trace = open(sys.argv[1]).readlines()

for line in trace:
    line = line.strip()
    assert line[0] == "(" and line[-1] == ")"
    line = line[1:-1]
    line = line.split(", ")
    dparser.load_call(line)

prelude = """
include "vale.i.dfy"
include "../../gen/impl/otbn/test.dfy"

module otbn_exe {
    import opened integers
    import opened ot_machine
    import opened ot_abstraction
    import opened addc512

method ExecuteDemo()
{
    var state := state.init();
"""

postlude = """
    state := state.debug_eval_code(va_code_mul_add_512());

}

method Main()
{
    ExecuteDemo();
}

}
"""

class State:
    def __init__(self):
        self.wdrs = dict()
        self.flgs = dict()

    def add_reg_update(self, reg, v):
        assert reg in REGS
        if reg not in self.wdrs:
            self.wdrs[reg] = [v]
        else:
            self.wdrs[reg].append(v)
    
    def add_flag_update(self, flag, value):
        if flag not in self.flgs:
            self.flgs[flag] = [value]
        else:
            self.flgs[flag].append(value)

    def add_fg_update(self, fg, value):
        assert fg in FGS
        value = int(value, base=16)
        self.add_flag_update(fg + "c", value & 1)
        self.add_flag_update(fg + "z", value & 8)

        # var r := if flags.cf then 1 else 0;
        # var r := r + if flags.msb then 2 else 0;
        # var r := r + if flags.lsb then 4 else 0;
        # r + if flags.zero then 8 else 0



def print_wdr(r):
    if r[0] == "w":
        return "WDR(" + r[1:] + ")"
    assert False

def match_formals(vproc, dproc):
    assert (len(vproc.formals) == len(dproc.formals))
    assert (set(vproc.formals.keys()) == set(dproc.formals))
    
    state = State()

    for name, gv in vproc.formals.items():
        value = dproc.get_formal_concrete_value(name)
        reg = print_wdr(gv.pyhsical)
        print("state := state.write_reg256(%s, %s);" % (reg, value))
        state.add_reg_update(gv.pyhsical, value)
    return state

print(prelude)
state = match_formals(vproc, dproc)
print(postlude)

trace2 = open(sys.argv[2]).readlines()

def parse_trace(state, line):
    line = line.strip().split(":")
    operand = line[0]
    value = line[1].split(",")[1]
    if operand[0] == "w":
        state.add_reg_update(operand, value)
    elif operand[0] == "f":
        state.add_fg_update(operand, value)
    else:
        assert False  

for line in trace2:
    parse_trace(state, line)

print(state.wdrs)
print(state.flgs)
# for method in self.methods.values():
#     print(method.calls)

    # p.load_trace("Generated/out.trace")
