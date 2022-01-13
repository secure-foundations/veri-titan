import enum
from re import match
import sys, ast, os
from ValeParser import *
from DfyParser import DafnyParser
from ValeParser import *
import time

SIM_PROLOGUE = """
include "../../arch/otbn/vale.i.dfy"
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

SIM_EPILOGUE = """
    state := state.debug_eval_code(va_code_mul_add_512());
}

method Main()
{
    ExecuteDemo();
}
}
"""

DFY_MOD_PATH = "tools/dafny_mod/Binaries/Dafny"

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
        self.add_flag_update(fg + "c", str(value & 1))
        self.add_flag_update(fg + "z", str(value & 8))

    def match_invocation(self, formals, invocation, matching):
        for argi, target_value in enumerate(invocation):
            formal = formals[argi]
            matched = set()
            for reg, values in self.wdrs.items():
                for index, value in enumerate(values):
                    if value == target_value:
                        matched |= {(reg, index)}
            
            if matched == set():
                for flag, values in self.flgs.items():
                    for index, value in enumerate(values):
                        if value == target_value:
                            matched |= {(flag, index)}

            # assert matched != set()
            if formal not in matching:
                matching[formal] = matched
            else:
                matching[formal] &= matched

            # print(formal, matched, target_value)
            print(matching[formal])

def print_wdr(r):
    if r[0] == "w":
        return "WDR(" + r[1:] + ")"
    assert False

def match_arguments(vproc, dproc):
    # list of formals have to match
    assert (len(vproc.formals) == len(dproc.formals))
    assert (set(vproc.formals.keys()) == set(dproc.formals))
    
    state = State()
    sim_code = ""

    for name, gv in vproc.formals.items():
        value = dproc.get_formal_concrete_value(name)
        reg = print_wdr(gv.pyhsical)
        sim_code += "state := state.write_reg256(%s, %s);\n" % (reg, value)
        state.add_reg_update(gv.pyhsical, value)
    sim_code = SIM_PROLOGUE + sim_code + SIM_EPILOGUE
    return sim_code, state

def run_instrumented_dfy(dfy_trace_file_path):
    os.system("dotnet experiment/dafny/Instrumented.dll > %s" % dfy_trace_file_path)
    time.sleep(1)

VALE_OUTPUT_DIR = "experiment/vale/"

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

def run_simulated_vad(sim_file_name, sim_code, vad_trace_file_path):
    sim_file_path = VALE_OUTPUT_DIR + sim_file_name
    sim_dfy_file = open(sim_file_path, "w+")
    sim_dfy_file.write(sim_code)
    sim_dfy_file.close()
    os.system(f"cd {VALE_OUTPUT_DIR} && dafny {sim_file_name} /noNLarith /timeLimit:20")
    dll_file_name = sim_file_name.replace(".dfy", ".dll")
    os.system(f"dotnet {VALE_OUTPUT_DIR + dll_file_name} > {vad_trace_file_path}")

if __name__ == '__main__':
    target_name = "dw_add"

    matching = dict()

    for i in range(5):
        dparser = DafnyParser(target_name, "experiment/dafny/dfy.ast")
        dproc = dparser.get_target_method()

        vproc = ValeProc("experiment/vale.ast")
        assert (vproc.name == target_name)

        dfy_trace_file_path = "experiment/dfy_trace"
        run_instrumented_dfy(dfy_trace_file_path)

        dparser.load_trace(dfy_trace_file_path)

        sim_code, state = match_arguments(vproc, dproc)

        vad_trace_file_path = "experiment/vad_trace"
        sim_file_name = "sim.dfy"

        run_simulated_vad(sim_file_name, sim_code, vad_trace_file_path) 

        trace = open(vad_trace_file_path).readlines()

        for line in trace:
            parse_trace(state, line)

        lemma = dparser.get_lemma("dw_add_correct")
        state.match_invocation(lemma.formals, lemma.traces[0], matching)
