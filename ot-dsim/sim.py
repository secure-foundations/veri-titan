# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
from bignum_lib.instructions import *
from bignum_lib.sim_helpers import read_dmem_from_file
from bignum_lib.sim_helpers import ins_objects_from_asm_file
from bignum_lib.sim_helpers import ins_objects_from_hex_file


def main():
    argparser = argparse.ArgumentParser(description='Bignum coprocessor instruction simulator')
    argparser.add_argument('-d', '--dmem-file', help="File width data memory")
    argparser.add_argument('-s', '--start-address', help='Start address in instruction memory')
    argparser.add_argument('-e', '--stop-address', help='Stop address in instruction memory')
    argparser.add_argument('-b', '--init-break', help='Set breakpoint at start address', action='store_true')
    mutexgroup_input_file = argparser.add_mutually_exclusive_group(required=True)
    mutexgroup_input_file.add_argument('-x', '--hex-file', help='Input hex file')
    mutexgroup_input_file.add_argument('-a', '--asm-file', help='Input assembly file')
    argparser.parse_args()
    args = argparser.parse_args()

    dmem = []
    if args.dmem_file:
        try:
            dmemfile = open(args.dmem_file)
            dmem = read_dmem_from_file(dmemfile)
            dmemfile.close()
        except IOError:
            print('Could not open file ' + args.infile)
            exit()
    else:
        print("Warning: No dmem init file given")

    if args.stop_address:
        if not args.stop_address.isdigit():
            raise Exception('Invalid stop address. Literals not supported as stop addresses.')
        stop_addr = int(args.stop_address)
        if stop_addr < 0 or stop_addr >= Machine.IMEM_DEPTH:
            raise Exception('Stop address out of range')

    ins_ctx = None
    start_addr = None
    stop_addr = None
    ins_objects = []

    asm_mode = False
    if args.asm_file:
        asm_mode = True
        try:
            asm_file = open(args.asm_file)
            ins_objects, ins_ctx, breakpoints = ins_objects_from_asm_file(asm_file)
            asm_file.close()
        except IOError:
            print('Could not open file ' + args.asm_file)
            exit()

        if args.start_address:
            if not args.start_address.isdigit():
                from_function = None
                from_label = None
                start_addr = 0
                try:
                    from_function = ins_ctx.get_function_addr_from_name(args.start_address)
                except KeyError:
                    pass
                if from_function:
                    start_addr = from_function
                else:
                    try:
                        from_label = ins_ctx.get_label_addr_from_name(args.start_address)
                    except KeyError:
                        pass
                    if from_label:
                        start_addr = from_label
                if not start_addr:
                    raise Exception('Start address for function/label ' + args.start_address
                                    + ' not found. Not a function or label name.')

    if args.hex_file:
        try:
            insfile = open(args.hex_file)
            ins_objects = ins_objects_from_hex_file(insfile)
            insfile.close()
        except IOError:
            print('Could not open file ' + args.insfile)
            exit()

    if args.start_address:
        if not args.start_address.isdigit():
            if not asm_mode:
                raise Exception('Invalid start address. Literal addresses only possible with assembly input')
        else:
            start_addr = int(args.start_address)
            if start_addr < 0 or start_addr >= Machine.IMEM_DEPTH:
                raise Exception('Start address out of range')
    else:
        start_addr = 0
        print("Warning: No explicit start address given. Starting at Imem[0]")

    machine = Machine(dmem, ins_objects, start_addr, stop_addr, ins_ctx, breakpoints=breakpoints)

    if args.init_break:
        machine.toggle_breakpoint(start_addr)

    if len(ins_objects) == 0:
        raise Exception('No code to execute, check input file content')

    cont = True
    inst_cnt = 0
    cycle_cnt = 0
    while cont:
        log_str = 'imem: ' + str(machine.get_pc()) + ', #ins: ' + str(inst_cnt)
        cont, trace_str, cycles = machine.step()
        print(trace_str + ' (' + log_str + ')')
        inst_cnt += 1
        cycle_cnt += cycles

    print('\n')
    print(machine.get_all_flags_table())
    print('\n')
    print(machine.get_all_reg_table(True))
    print('\nDMEM:')
    print(machine.get_dmem_table(0, 119))


if __name__ == "__main__":
    main()
