# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import logging
from bignum_lib.sim_helpers import ins_objects_from_asm_file
from bignum_lib.disassembler import Disassembler
from bignum_lib.instructions import ILoop
from bignum_lib.instructions_ot import IOtLoop
from bignum_lib.instructions_ot import IOtLoopi
from bignum_lib.instructions_ot import IOtJal
from bignum_lib.instructions import ICall
from bignum_lib.instructions_ot import IOtBeq
from bignum_lib.instructions_ot import IOtBne
from bignum_lib.instructions import IBranch
from bignum_lib.instructions_ot import IOtLui
from bignum_lib.instructions_ot import IOtAddi
from bignum_lib.instructions import IMovi

def handle_movi_combined(ins1, ins2):
    return


def main():
    logging.basicConfig(level=logging.DEBUG)
    argparser = argparse.ArgumentParser(description='Dcrypto to OTBN assembly converter')
    argparser.add_argument('infile', help="Input Assembly file")
    argparser.add_argument('-a', '--addresses',
                           help='print address for each instruction',
                           action='store_true')
    argparser.add_argument('-w', '--dmem-word-addressing',
                           help='use WLEN word addressing for dmem instead of byte addressing',
                           action='store_true')
    argparser.parse_args()
    args = argparser.parse_args()

    try:
        infile = open(args.infile)
    except IOError:
        print('Could not open file ' + args.infile)
        exit()

    """Load binary executable from file"""
    byte_addressing = not args.dmem_word_addressing
    ins_objects, ctx, _ = ins_objects_from_asm_file(infile, dmem_byte_addressing=byte_addressing)
    infile.close()

    ins_objects_push = [0]*len(ins_objects)
    ins_objects_len = [1] * len(ins_objects)

    otbn_ins_obj_list = []

    ignore_next = False
    for idx, item in enumerate(ins_objects):
        if ignore_next:
            ignore_next = False
            continue

        # The movi instruction is a special case, since two (subsequent) instructions have to be considered together
        '''
        if isinstance(item, IMovi):
            if idx != len(ins_objects) - 1:
                if isinstance(ins_objects[idx+1], IMovi):
                    if item.rd == ins_objects[idx+1].rd and item.fun == ins_objects[idx+1].fun:
                        if item.slice != ins_objects[idx+1].slice:
                            # two subsequent movi instructions are adressing the same limb, one the lower 16b, one
                            # the upper 16b -> Handle them together to be replaced by one single combination of
                            # ADDI and LUI
                            logging.info('Combining two movi instructions (Address '
                                         + str(idx) + ' and ' + str(idx+1) + ').')
                            handle_movi_combined(item, ins_objects[idx+1])
                            otbn_ins_obj = item.convert_otbn(idx)
                            otbn_ins_obj_list.extend(otbn_ins_obj)
                            ignore_next = True
                            continue'''

        otbn_ins_obj = item.convert_otbn(idx)
        if otbn_ins_obj:
            otbn_ins_obj_list.extend(otbn_ins_obj)
            if len(otbn_ins_obj) > 1:
                ins_objects_len[idx] = len(otbn_ins_obj)
                ins_objects_push[idx+1:] = [i + len(otbn_ins_obj) - 1 for i in ins_objects_push[idx+1:]]
        else:
            otbn_ins_obj_list.append(item)

    #for item in otbn_ins_obj_list:
    #    print(item)

    # create list of new loopranges
    loopranges_otbn = []
    # iterate over existing loopranges and see if they have been relocated
    for item in ctx.loopranges:
        # we have to consider that the last instruction in a loop is now possibly longer than 1 instruction
        loopranges_otbn.append(range(item[0]+ins_objects_push[item[0]], item[-1] + ins_objects_push[item[-1]] + ins_objects_len[item[-1]]-1))

    # find loop instructions and adjust them
    for item in loopranges_otbn:
        # modify loop instructions
        ins = otbn_ins_obj_list[item[0]]
        if not (isinstance(ins, IOtLoopi) or isinstance(ins, IOtLoop) or isinstance(ins, ILoop)):
            raise Exception("Expected loop instruction")
        current_len = ins.len
        new_len = len(item)
        if current_len != new_len:
            logging.info('Extended loop length at (new) address ' + str(item[0]) + ' by ' + str(new_len-current_len)
                         + ' from ' + str(current_len) + ' to ' + str(new_len) + '.')
            ins.len = new_len

    # assign list with new loop ranges to context
    ctx.loopranges = loopranges_otbn

    # create new dictionary for labels {address:label)}
    # there are no dedicated function labels in otbn format
    labels_otbn = {}
    for item in ctx.labels:
        new_loc = ins_objects_push[item] + item
        if new_loc != item:
            logging.info('Relocating address of label ' + str(ctx.labels.get(item)) + ' from ' + str(item)
                     + ' to ' + str(new_loc) + '.')
        labels_otbn.update({new_loc:ctx.labels.get(item)})

    for item in ctx.functions:
        new_loc = ins_objects_push[item] + item
        if new_loc != item:
            logging.info('Relocating address of function ' + str(ctx.functions.get(item)) + ' from ' + str(item)
                     + ' to ' + str(new_loc) + '.')
        labels_otbn.update({new_loc:ctx.functions.get(item)})

    # adjust branch, call and jump instructions
    inv_labels = {v: k for k, v in labels_otbn.items()}
    for idx,item in enumerate(otbn_ins_obj_list):
        if isinstance(item, IOtBne) or isinstance(item, IOtBeq):
            if not item.label:
                raise Exception('No label associated with branch instruction at (new) address ' + str(idx) +
                                '. Cannot relocate')
            # set address
            item.addr = idx
            new_target_addr = inv_labels.get(item.label)
            new_offset = new_target_addr - item.addr
            if new_offset != item.offset:
                logging.info('Adjusting branch offset for branch instruction at (new) address ' + str(idx) + ' from '
                            + str(item.offset) + ' to ' + str(new_offset) + ' (for label '
                             + str(labels_otbn.get(new_target_addr)) + ')')
                item.offset = new_offset
        if isinstance(item, IBranch):
            if not item.label:
                raise Exception('No label associated with branch instruction at (new) address ' + str(idx) +
                                '. Cannot relocate')
            item.addr = idx
            new_target = inv_labels.get(item.label)
            if new_target != item.imm:
                logging.info('Adjusting branch target for branch instruction at (new) address ' + str(idx) + ' from '
                            + str(item.imm) + ' to ' + str(new_target) + ' (for label '
                             + str(labels_otbn.get(new_target)) + ')')
                item.imm = new_target
            item.addr = idx
        if isinstance(item, IOtJal):
            if not item.label:
                raise Exception('No function label associated with JAL instruction at (new) address ' + str(idx) +
                                '. Cannot relocate')
            item.addr = idx
            new_target_addr = inv_labels.get(item.label)
            new_offset = new_target_addr - item.addr
            if new_offset != item.imm:
                logging.info('Adjusting jump offset for JAL instruction at (new) address ' + str(idx) + ' from '
                            + str(item.imm) + ' to ' + str(new_offset) + ' (for label '
                             + str(inv_labels.get(new_target_addr)) + ')')
                item.imm = new_offset
        if isinstance(item, ICall):
            if not item.label:
                raise Exception('No function label associated with JAL instruction at (new) address ' + str(idx) +
                                '. Cannot relocate')
            item.addr = idx
            new_target_addr = inv_labels.get(item.label)
            if new_target_addr != item.imm:
                logging.info('Adjusting jump target for CALL instruction at (new) address ' + str(idx) + ' from '
                            + str(item.imm) + ' to ' + str(new_target_addr) + ' (for label '
                             + str(inv_labels.get(new_target_addr)) + ')')
                item.imm = new_target_addr
            item.addr = idx

    # assign new dictionary with {label addresses:labels} to context
    ctx.labels = labels_otbn

    disassembler = Disassembler.from_ins_objects_and_context(otbn_ins_obj_list, ctx)
    asm_lines = disassembler.create_assembly(opt_address=args.addresses, format='otbn')
    for item in asm_lines:
        print(item)


if __name__ == "__main__":
    main()
