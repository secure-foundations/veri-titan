# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
from bignum_lib.disassembler import Disassembler


def main():
    argparser = argparse.ArgumentParser(description='Bignum coprocessor instruction disassembler')
    argparser.add_argument('infile',
                           help="Input file")
    argparser.add_argument('-o', '--output-file',
                           help="Output file")
    argparser.add_argument('-l', '--labelfile',
                           help="Label file")
    argparser.add_argument('-b', '--bitmaps',
                           help='show extensive bitmaps for all instructions',
                           action='store_true')
    argparser.add_argument('--defines',
                           help='include defines for functions in c files (only works together with --code)',
                           action='store_true')
    argparser.add_argument('--code',
                           help='create c source style structure',
                           action='store_true')
    argparser.add_argument('-f', '--function-length',
                           help='include function length in function statements',
                           action='store_true')
    mutexgroup_addr = argparser.add_mutually_exclusive_group()
    mutexgroup_addr.add_argument('-ad', '--addresses-dec',
                                 help="Include leading decimal addresses",
                                 action="store_true")
    mutexgroup_addr.add_argument('-ax', '--addresses-hex',
                                 help="Include leading hexadecimal addresses",
                                 action="store_true")
    argparser.parse_args()
    args = argparser.parse_args()

    address = False
    address_format = None
    if args.addresses_dec:
        address = True
        address_format = 'dec'
    if args.addresses_hex:
        address = True
        address_format = 'hex'

    ins_lines = []
    label_lines = None
    if args.infile.startswith('0x'):
        ins_lines = [args.infile]
    else:
        try:
            insfile = open(args.infile)
            ins_lines = insfile.readlines()
            insfile.close()
        except IOError:
            print('Could not open file ' + args.infile)
            exit()
        if args.labelfile:
            try:
                labelfile = open(args.labelfile)
                label_lines = labelfile.readlines()
                labelfile.close()
            except IOError:
                print('Could not open file ' + args.labelfile)
                exit()

    dasm = Disassembler.from_hex_file_lines(ins_lines, label_lines, args.bitmaps)
    outlines = dasm.create_assembly(address, address_format, args.function_length, args.code, args.defines)

    if args.output_file:
        outfile = open(args.output_file, 'w')
        if len(outlines):
            outfile.write(outlines[0])
        if len(outlines) > 1:
            outfile.writelines('\n' + line for line in outlines[1:])
        outfile.close()
    else:
        for l_cnt in outlines:
            print(l_cnt)


if __name__ == "__main__":
    main()
