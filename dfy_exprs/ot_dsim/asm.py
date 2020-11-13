# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
from bignum_lib.assembler import Assembler


def main():
    argparser = argparse.ArgumentParser(description='Bignum coprocessor instruction assembler')
    argparser.add_argument('infile', help="Input file")
    argparser.add_argument('-o', '--out-hex-file', help='Output hex file to store assembled binary instructions')
    argparser.add_argument('--out-asm', help='Output reconstructed assembly instead of hex', action='store_true')
    argparser.add_argument('--nosummary', help="Do not print summary", action='store_true')
    argparser.parse_args()
    args = argparser.parse_args()

    try:
        infile = open(args.infile)
    except IOError:
        print('Could not open file ' + args.infile)
        exit()

    lines = infile.readlines()

    a = Assembler(lines)

    if not args.nosummary:
        a.print_summary()

    a.assemble()

    if args.out_hex_file:
        outfile = open(args.out_hex_file, 'w+')
        if len(a.get_instruction_words()):
            outfile.write('0x' + hex(a.get_instruction_words()[0])[2:].zfill(8))
        if len(a.get_instruction_words()) > 1:
            outfile.writelines('\n' + '0x' + hex(item)[2:].zfill(8) for item in a.get_instruction_words()[1:])
        outfile.close()
    else:
        for item in a.get_instruction_objects():
            if args.out_asm:
                print(item.get_asm_str())
            else:
                print('0x' + hex(item.ins)[2:].zfill(8))


if __name__ == "__main__":
    main()
