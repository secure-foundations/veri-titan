# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from . assembler import Assembler
from . disassembler import Disassembler
from . machine import Machine

from collections import Counter
from tabulate import tabulate


def read_dmem_from_file(dmemfile):
    line_cnt = 0
    dmem = []
    while True:
        line_str = dmemfile.readline()
        if not line_str:
            break
        if line_cnt == Machine.DMEM_DEPTH:
            raise OverflowError('Dmem file to large')
        if ':' in line_str:
            addr = line_str.split(':')[0].strip()
            if int(addr) != line_cnt:
                raise Exception('Error in Dmem file line ' + str(line_cnt+1)
                                + ' (non continues mem files currently not supported)')
            line_str = line_str.split(':')[1].lower().strip()
        words = line_str.split()
        if len(words) != 8:
            raise Exception('Error in Dmem file line ' + str(line_cnt+1)
                            + ' 8 32-bit words expected per line, found ' + str(len(words)) + '.')
        line_str = ''.join(words)
        if len(line_str) != 32*2:
            raise Exception('Error in Dmem file line ' + str(line_cnt+1) + '. Expecting data 32 bytes per line. Found '
                            + str(len(line_str)) + ' characters.')
        dmem.append(int(line_str, 16))
        line_cnt += 1
    return dmem


def ins_objects_from_hex_file(hex_file):
    lines = hex_file.readlines()
    disassembler = Disassembler.from_hex_file_lines(lines)
    return disassembler.get_instruction_objects(), disassembler.ctx


def ins_objects_from_asm_file(asm_file, dmem_byte_addressing=False, otbn_only=False):
    lines = asm_file.readlines()
    assembler = Assembler(lines, dmem_byte_addressing=dmem_byte_addressing, otbn_only=otbn_only)
    assembler.assemble()
    return assembler.get_instruction_objects(), assembler.get_instruction_context(), assembler.breakpoints

def dump_instruction_histo(instruction_histo, sort_by="key"):
    if sort_by == "key":
        data = sorted(instruction_histo.items())
    elif sort_by == "value":
        data = instruction_histo.most_common()
    else:
        assert True

    print(tabulate(data, headers=["instruction", "count"]))

def dump_function_call_stats(func_calls):
    # Build function call graphs and a call site index
    # caller-index == forward, callee-indexed == reverse
    # The call graphs are on function granularity; the call sites dictionary is
    # indexed by the called function, but uses the call site as value.
    callgraph = {}
    rev_callgraph = {}
    rev_callsites = {}
    for c in func_calls:
        if c['caller_func'] not in callgraph:
            callgraph[c['caller_func']] = Counter()
        callgraph[c['caller_func']][c['callee_func']] += 1

        if c['callee_func'] not in rev_callgraph:
            rev_callgraph[c['callee_func']] = Counter()
        rev_callgraph[c['callee_func']][c['caller_func']] += 1

        if c['callee_func'] not in rev_callsites:
            rev_callsites[c['callee_func']] = Counter()
        rev_callsites[c['callee_func']][c['call_site']] += 1

    total_leaf_calls = 0
    total_calls_to_funcs_with_one_callsite = 0
    total_func_calls = 0
    for rev_callee_func, rev_caller_funcs in rev_callgraph.items():
        has_one_callsite = False
        print("Function at address {callee}".format(callee=rev_callee_func))
        print("  is called from the following functions")
        for rev_caller_func, cnt in rev_caller_funcs.most_common():
            print("    * {cnt} times by function at address {rev_caller_func}".
                  format(rev_caller_func=rev_caller_func, cnt=cnt))
        print("  from the following call sites")
        for rev_callsite, cnt in rev_callsites[rev_callee_func].most_common():
            print("    * {cnt} times from address {rev_callsite}".format(
                rev_callsite=rev_callsite, cnt=cnt))

        has_one_callsite = len(rev_callsites[rev_callee_func]) == 1

        print("  calls")
        if rev_callee_func not in callgraph:
            print("    no other function (leaf function).")

            if not has_one_callsite:
                # We don't count it as leaf function call if it has only one
                # call site to prevent double-counting these as optimization
                # opportunity.
                total_leaf_calls += sum(rev_caller_funcs.values())
        else:
            caller_funcs = callgraph[rev_callee_func]
            for caller_func, cnt in caller_funcs.most_common():
                print("    * {cnt} times function at address {caller}".format(
                    caller=caller_func, cnt=cnt))
        print()

        if has_one_callsite:
            total_calls_to_funcs_with_one_callsite += rev_caller_funcs.most_common(
            )[0][1]

        total_func_calls += sum(rev_caller_funcs.values())
    print()

    # Function call statistics
    total_calls_req_call = total_func_calls - total_leaf_calls - total_calls_to_funcs_with_one_callsite
    print(
        "Of a total of {total_func_calls} function calls, there were ".format(
            total_func_calls=total_func_calls))
    print(
        "  {total_calls_to_funcs_with_one_callsite} function calls to a function with only one call site (call/ret can be replaced with static jumps)"
        .format(total_calls_to_funcs_with_one_callsite=
                total_calls_to_funcs_with_one_callsite))
    print(
        "  {total_leaf_calls} leaf function calls (no function prologue/epilogue needed)"
        .format(total_leaf_calls=total_leaf_calls))
    print(
        "Overall, {total_calls_req_call} of {total_func_calls} ({percent:.02f} percent) need full function call semantics."
        .format(total_func_calls=total_func_calls,
                total_calls_req_call=total_calls_req_call,
                percent=total_calls_req_call / total_func_calls * 100))


def dump_loop_stats(loops):
    loop_cnt = len(loops)
    loop_len_values = [l['loop_len'] for l in loops]
    loop_len_min = min(loop_len_values)
    loop_len_max = max(loop_len_values)
    loop_len_avg = sum(loop_len_values) / loop_cnt

    loop_iterations_values = [l['iterations'] for l in loops]
    loop_iterations_min = min(loop_iterations_values)
    loop_iterations_max = max(loop_iterations_values)
    loop_iterations_avg = sum(loop_iterations_values) / loop_cnt

    print("Loops: {loop_cnt}".format(loop_cnt=loop_cnt))
    print(
        "Loop body length (instructions): min: {loop_len_min}, max: {loop_len_max}, avg: {loop_len_avg:.02f}"
        .format(loop_len_min=loop_len_min,
                loop_len_max=loop_len_max,
                loop_len_avg=loop_len_avg))
    print(
        "Number of iterations: min: {loop_iterations_min}, max: {loop_iterations_max}, avg: {loop_iterations_avg:.02f}"
        .format(loop_iterations_min=loop_iterations_min,
                loop_iterations_max=loop_iterations_max,
                loop_iterations_avg=loop_iterations_avg))


def dump_movi_stats(movi_stats):
    imm_le_12 = sum(
        [cnt for size, cnt in movi_stats.most_common() if size <= 12])
    movi_calls = sum(movi_stats.values())
    print(
        "{movi_calls} calls to movi, {imm_le_12} ({percent:.02f} percent) with an immediate <= 12 bit"
        .format(imm_le_12=imm_le_12,
                movi_calls=movi_calls,
                percent=imm_le_12 / movi_calls * 100))


def dump_wide_mem_op_stats(wide_mem_ops):
    mem_op_cnt = len(wide_mem_ops)
    inc_ops = sum([s['inc_src'] + s['inc_dst'] for s in wide_mem_ops])
    one_inc_ops = sum([s['inc_src'] ^ s['inc_dst'] for s in wide_mem_ops])
    two_inc_ops = sum([s['inc_src'] and s['inc_dst'] for s in wide_mem_ops])
    print("{mem_op_cnt} ld/st memory operations".format(mem_op_cnt=mem_op_cnt))
    print("{inc_ops} increment operations, on average {inc_avg:.02f} incs/op".
          format(inc_ops=inc_ops, inc_avg=inc_ops / mem_op_cnt))
    print(
        "{one_inc_ops} operations have only one increment ({inc_avg:.02f} percent of all wide memory ops)"
        .format(one_inc_ops=one_inc_ops,
                inc_avg=one_inc_ops / mem_op_cnt * 100))
    print(
        "{two_inc_ops} operations have two increments ({inc_avg:.02f} percent of all wide memory ops)"
        .format(two_inc_ops=two_inc_ops,
                inc_avg=two_inc_ops / mem_op_cnt * 100))


def dump_flag_access_stats(flag_access):
    if len(flag_access) == 0:
        print("No flag accesses.")
        return

    flag_access_cnt = len(flag_access)
    n_access_cnt = len([x for x in flag_access if x['flag_group'] == 'n'])
    x_access_cnt = len([x for x in flag_access if x['flag_group'] == 'x'])

    prev_group = flag_access[0]['flag_group']
    group_switch_cnt = 0
    for f in flag_access:
        group_switch_cnt += f['flag_group'] != prev_group
        prev_group = f['flag_group']

    print(
        "{flag_access_cnt} accesses to flags as part of an instruction execution, of which"
        .format(flag_access_cnt=flag_access_cnt))
    print(
        "- {n_access_cnt} ({percent:.02f} percent) accesses were to the normal flag group"
        .format(n_access_cnt=n_access_cnt,
                percent=n_access_cnt / flag_access_cnt * 100))
    print(
        "- {x_access_cnt} ({percent:.02f} percent) accesses were to the extended (X) flag group"
        .format(x_access_cnt=x_access_cnt,
                percent=x_access_cnt / flag_access_cnt * 100))
    print(
        "{group_switch_cnt} instructions used a different flag group than the previous access"
        .format(group_switch_cnt=group_switch_cnt))


def dump_stats(stats, config):
    print("Instruction frequencies")
    print("-----------------------")
    dump_instruction_histo(stats['instruction_histo'], config['instruction_histo_sort_by'])
    print()

    print("Function call statistics")
    print("------------------------")
    if 'func_calls' in stats:
        dump_function_call_stats(stats['func_calls'])
    else:
        print("No function calls found.")
    print()

    print("Loop statistics")
    print("---------------")
    if 'loops' in stats:
        dump_loop_stats(stats['loops'])
    else:
        print("No loops found.")
    print()

    print("Movi statistics")
    print("---------------")
    if 'movi' in stats:
        dump_movi_stats(stats['movi'])
    else:
        print("No movi instructions found.")
    print()

    print("Wide load/store statistics")
    print("--------------------------")
    if 'wide_mem_ops' in stats:
        dump_wide_mem_op_stats(stats['wide_mem_ops'])
    else:
        print("No wide memory operations found.")
    print()

    print("Flag statistics")
    print("---------------")
    if 'flag_access' in stats:
        dump_flag_access_stats(stats['flag_access'])
    else:
        print("No flag accesses found.")
    print()

def print_test_headline(nr, cnt, desc):
    headline = "Running test %d/%d: %s" % (nr, cnt, desc)
    print(headline + "\n" + "=" * len(headline) + "\n")

def all_instructions():
    return [
        "add",
        "addc",
        "addcx",
        "addi",
        "addm",
        "addx",
        "and",
        "b",
        "bl",
        "bnc",
        "bnz",
        "bz",
        "call",
        "cmp",
        "cmpbx",
        "ld",
        "lddmp",
        "ldi",
        "ldlc",
        "ldr",
        "ldmod",
        "ldrfp",
        "ldrnd",
        "loop",
        "mov",
        "movi",
        "mul128",
        "nop",
        "not",
        "or",
        "ret",
        "rshi",
        "selc",
        "selcx",
        "sell",
        "sellx",
        "selm",
        "sigini",
        "st",
        "stdmp",
        "stmod",
        "strnd",
        "sub",
        "subb",
        "subbx",
        "subi",
        "subm",
        "subx",
        "xor",
    ]

def init_stats():
    stats = {}
    stats['instruction_histo'] = Counter()
    for i in all_instructions():
        stats['instruction_histo'][i] = 0
    return stats
