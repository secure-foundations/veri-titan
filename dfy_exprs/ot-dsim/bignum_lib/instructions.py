# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from . machine import *
from . instructions_ot import IBnAdd
from . instructions_ot import IBnAddi
from . instructions_ot import IBnAddc
from . instructions_ot import IBnSub
from . instructions_ot import IBnSubb
from . instructions_ot import IBnSubi
from . instructions_ot import IBnAnd
from . instructions_ot import IBnOr
from . instructions_ot import IBnXor
from . instructions_ot import IBnNot
from . instructions_ot import IBnAddm
from . instructions_ot import IBnSubm
from . instructions_ot import IBnMulh
from . instructions_ot import IBnCmp
from . instructions_ot import IBnCmpb
from . instructions_ot import IBnRshi
from . instructions_ot import IBnSel
from . instructions_ot import IBnMov
from . instructions_ot import IBnMovr
from . instructions_ot import IBnLid
from . instructions_ot import IBnSid
from . instructions_ot import IBnWsrrw

from . instructions_ot import IOtLoopi
from . instructions_ot import IOtLoop
from . instructions_ot import IOtAddi
from . instructions_ot import IOtAndi
from . instructions_ot import IOtJal
from . instructions_ot import IOtJalr
from . instructions_ot import IOtBne
from . instructions_ot import IOtBeq
from . instructions_ot import IOtCsrrs
from . instructions_ot import IOtCsrrw
from . instructions_ot import IOtLui

import logging


def _get_imm(asm_str):
    """return int for immediate string and check proper formatting (e.g "#42")"""
    if len(asm_str.split()) > 1:
        raise SyntaxError('Unexpected separator in immediate')
    if not asm_str.startswith('#'):
        raise SyntaxError('Missing \'#\' character at start of immediate')
    if not asm_str[1:].isdigit():
        raise SyntaxError('Immediate not a number')
    return int(asm_str[1:])


def _get_limb(asm_str):
    """returns limb for immediate string and check proper formatting (e.g."*5")"""
    if len(asm_str.split()) > 1:
        raise SyntaxError('Unexpected separator in limb reference')
    if not asm_str.startswith('*'):
        raise SyntaxError('Missing \'*\' character at start of limb reference')
    if not asm_str[1:].isdigit():
        raise SyntaxError('limb reference not a number')
    return int(asm_str[1:])


def _get_index_imm(asm_str):
    """returns the index from an immediate index notation (e.g "[42]")"""
    if not asm_str.startswith('['):
        raise SyntaxError('Missing \'[\' character at start of index notation')
    if not asm_str.endswith(']'):
        raise SyntaxError('Missing \']\' character at end of index notation')
    return _get_imm(asm_str[1:-1].strip())


def _get_single_reg(asm_str):
    """returns a single register from string and check proper formatting (e.g "r5")"""
    if len(asm_str.split()) > 1:
        raise SyntaxError('Unexpected separator in reg reference')
    if not asm_str.lower().startswith('r'):
        raise SyntaxError('Missing \'r\' character at start of reg reference')
    if not asm_str[1:].isdigit():
        raise SyntaxError('reg reference not a number')
    return int(asm_str[1:])


def _get_single_limb(asm_str):
    """returns a single limb with a potential increment (e.g "*6++" or "*7")"""
    if len(asm_str.split()) > 1:
        raise SyntaxError('Unexpected separator in limb reference')
    if not asm_str.startswith('*'):
        raise SyntaxError('Missing \'*\' character at start of limb reference')
    if asm_str.endswith('++'):
        inc = True
        limb = asm_str[1:-2]
    else:
        inc = False
        limb = asm_str[1:]
    if not limb.isdigit():
        raise SyntaxError('limb reference not a number')
    return int(limb), inc


def _get_single_reg_and_index_imm(asm_str):
    """decode a single reg and an immediate index (e.g. "r15, [#7]")"""
    substr = asm_str.split(',')
    if len(substr) != 2:
        raise SyntaxError('Syntax error in parameter set. Expected register and indexed immediate')
    reg = _get_single_reg(substr[0].strip())
    idx = _get_index_imm(substr[1].strip())
    return reg, idx


def _get_double_limb(asm_str):
    """decode a double limb notation (e.g. "*6++, *8")"""
    substr = asm_str.split(',')
    if len(substr) != 2:
        raise SyntaxError('Syntax error in parameter set. Expected two limb references')
    limbl, incl = _get_single_limb(substr[0].strip())
    limbr, incr = _get_single_limb(substr[1].strip())
    return limbl, incl, limbr, incr


def _get_double_reg(asm_str):
    """decode a double reg notation without shift (e.g. "r1, r2")"""
    substr = asm_str.split(',')
    if len(substr) != 2:
        raise SyntaxError('Syntax error in parameter set. Expected two reg references')
    regl = _get_single_reg(substr[0].strip())
    regr = _get_single_reg(substr[1].strip())
    return regl, regr


def _get_double_reg_with_imm(asm_str):
    """decode a double reg with immediate (e.g. "r3, r5, #254")"""
    substr = asm_str.split(',')
    if len(substr) != 3:
        raise SyntaxError('Syntax error in parameter set. Expected two reg references and immediate')
    rd = _get_single_reg(substr[0].strip())
    rs = _get_single_reg(substr[1].strip())
    imm = _get_imm(substr[2].strip())
    return rd, rs, imm


def _get_triple_reg(asm_str):
    """decode a triple reg notation without shift (e.g. "r1, r2, r3")"""
    substr = asm_str.split(',')
    if len(substr) != 3:
        raise SyntaxError('Syntax error in parameter set. Expected two reg references')
    rd = _get_single_reg(substr[0].strip())
    rs1 = _get_single_reg(substr[1].strip())
    rs2 = _get_single_reg(substr[2].strip())
    return rd, rs1, rs2


def _get_single_shifted_reg(asm_str):
    """decode a reg in (possible) shift notation (e.g. "r4 >> 128")"""
    if '>>' in asm_str:
        shift_right = True
        substr = asm_str.split('>>')
    elif '<<' in asm_str:
        shift_right = False
        substr = asm_str.split('<<')
    else:
        return _get_single_reg(asm_str), False, 0

    if len(substr) != 2:
        raise SyntaxError('Syntax error in parameter set in input shift notation. '
                          'Expected reg and shift immediate')

    reg = _get_single_reg(substr[0].strip())
    shift_bits = substr[1].strip()

    if len(shift_bits.split()) > 1:
        raise SyntaxError('Unexpected separator in shift immediate reference')

    if not shift_bits.isdigit():
        raise SyntaxError('input shift immediate not a number')

    return reg, shift_right, int(shift_bits)


def _get_single_reg_with_section(asm_str):
    """decode a reg with indication a upper/lower section (e.g. "r21l" or "r23u")"""
    if asm_str.endswith('u'):
        upper = True
    elif asm_str.endswith('l'):
        upper = False
    else:
        raise SyntaxError('Expecting \'u\' or \'l\' at end of register reference '
                          'with section indication')
    reg = _get_single_reg(asm_str[:-1].strip())
    return reg, upper


def _get_limb_section(asm_str):
    """decode the limb and the section (h or l) from limb (e.g "4l")"""
    if len(asm_str.split()) > 1:
        raise SyntaxError('Unexpected separator in limb reference')
    if asm_str.lower().endswith('l'):
        s = 0
    elif asm_str.lower().endswith('h'):
        s = 1
    else:
        raise SyntaxError('Expecting \'l\' or \'h\' at the end of limb section reference')
    limb = asm_str[:-1]
    if not limb.isdigit():
        raise SyntaxError('reg reference not a number')
    return int(limb), s


def _get_reg_with_limb(asm_str):
    """decode reference to 16 bit section of a register's limb (e.g "r15.3l")"""
    substr = asm_str.split('.')
    if len(substr) != 2:
        raise SyntaxError('Syntax error in parameter set. Expected reference to 16 bit '
                          'section of limb (e.g. \"r12.3l\")')
    reg = _get_single_reg(substr[0].strip())
    limb, s = _get_limb_section(substr[1].strip())
    return reg, limb, s


def _get_reg_limb_and_imm(asm_str):
    """decode the movi notation (reg+limb reference + immediate, e.g.: "r15.3l, #42" )"""
    substr = asm_str.split(',')
    if len(substr) != 2:
        raise SyntaxError('Syntax error in parameter set. Expected reg with limb + immediate')
    reg, limb, s = _get_reg_with_limb(substr[0].strip())
    imm = _get_imm(substr[1].strip())
    return reg, limb, s, imm


def _get_limb_with_paren(asm_str):
    """decode limb from a notation with parentheses as it is used in loop instructions (e.g "*0 (")"""
    if not asm_str.endswith('('):
        raise SyntaxError('Expecting \'(\'')
    return _get_limb(asm_str[:-1].strip())


def _get_imm_with_paren(asm_str):
    """decode immediate from a notation with parentheses as it is used in loop instructions (e.g "#4 (")"""
    if not asm_str.endswith('('):
        raise SyntaxError('Expecting \'(\'')
    return _get_imm(asm_str[:-1].strip())


def _get_loop_type_direct(asm_str):
    """decode loop type"""
    if asm_str.startswith('*'):
        return False
    elif asm_str.startswith('#'):
        return True
    else:
        raise SyntaxError('Syntax error in loop notation')


def _get_three_regs_with_shift(asm_str):
    """decode the full standard format with rd, rs1 and possibly shifted rs2 (e.g.: "r21, r5, r7 >> 128")"""
    substr = asm_str.split(',')
    if len(substr) != 3:
        raise SyntaxError('Syntax error in parameter set. Expected three reg references')
    rd = _get_single_reg(substr[0].strip())
    rs1 = _get_single_reg(substr[1].strip())
    rs2, shift_right, shift_bits = _get_single_shifted_reg(substr[2].strip())
    return rd, rs1, rs2, shift_right, shift_bits


def _get_two_regs_with_shift(asm_str):
    """decode standard format with possibly shifted rs but only a single source register (e.g.: "r21, r7 >> 128")"""
    substr = asm_str.split(',')
    if len(substr) != 2:
        raise SyntaxError('Syntax error in parameter set. Expected two reg references')
    rd = _get_single_reg(substr[0].strip())
    rs, shift_right, shift_bits = _get_single_shifted_reg(substr[1].strip())
    return rd, rs, shift_right, shift_bits


def _get_three_regs_with_sections(asm_str):
    """decode a notation with three regs, with indicating a upper and lower section for the source regs
    this is used with the mul instruction (e.g.: "r24, r29l, r21u")"""
    substr = asm_str.split(',')
    if len(substr) != 3:
        raise SyntaxError('Syntax error in parameter set. Expected three reg references')
    rd = _get_single_reg(substr[0].strip())
    rs1, rs1_upper = _get_single_reg_with_section(substr[1].strip())
    rs2, rs2_upper = _get_single_reg_with_section(substr[2].strip())
    return rd, rs1, rs1_upper, rs2, rs2_upper


class UnknownOpcodeError(KeyError):
    pass


class InvalidOp2(ValueError):
    pass


class InsContext(object):
    instructions = {}
    functions = {}
    labels = {}
    loopranges = []
    functioncnt = 0
    labelcnt = 0
    dmem_byte_addressing = False

    def get_or_add_function(self, addr):
        if addr not in self.functions:
            self.functions.update({addr: 'fun' + str(self.functioncnt)})
            self.functioncnt += 1
        return self.functions[addr]

    def get_or_add_label(self, addr):
        if addr not in self.labels:
            self.labels.update({addr: 'label' + str(self.labelcnt)})
            self.labelcnt += 1
        return self.labels[addr]

    def get_function_addr_from_name(self, name):
        return {v: k for k, v in self.functions.items()}[name]

    def get_label_addr_from_name(self, name):
        return {v: k for k, v in self.labels.items()}[name]


class AsmCtx:
    def __init__(self, functions, loopclose, labels, dmem_byte_addressing=False):

        # function_name : (addr,[len])
        # Dictionary with function name as key, referring to tuple of addr and optional length
        self.functions = functions

        # Mapping of loop closings (open address (loop instruction) -> loop closing ( ')' character) )
        self.loopclose = loopclose

        # Dictionary of labels (label -> addr)
        self.labels = labels

        self.ins_ctx = InsContext()
        self.ins_ctx.functions.clear()
        for k in functions:
            if isinstance(functions[k], tuple):
                self.ins_ctx.functions.update({functions[k][0]: k})
            else:
                self.ins_ctx.functions.update({functions[k]: k})
        self.ins_ctx.loopranges = [range(k, v) for k, v in loopclose.items()]
        self.ins_ctx.labels = {v: k for k, v in labels.items()}
        self.ins_ctx.dmem_byte_addressing = dmem_byte_addressing

    def get_addr_for_function_name(self, fun_str, format='std'):
        """return destination address for function name (as parameter) and check proper formatting"""
        if len(fun_str.split()) > 1:
            raise SyntaxError('Unexpected separator in function name')
        if format == 'ot':
            dest_addr = self.functions.get(fun_str)[0]
        else:
            if not fun_str.startswith('&'):
                raise SyntaxError('Missing \'&\' in function name parameter')
            dest_addr = self.functions.get(fun_str[1:])[0]
        if dest_addr is None:
            raise Exception('Undefined function: ' + fun_str[1:])
        return dest_addr

    def get_addr_for_label(self, label_str):
        """return destination address for label (as parameter) and check proper formatting"""
        if len(label_str.split()) > 1:
            raise SyntaxError('Unexpected separator in label')
        dest_addr = self.labels.get(label_str)
        if dest_addr is None:
            raise Exception('Undefined label: ' + label_str)
        return dest_addr

    def get_loop_close_addr(self, addr):
        return self.loopclose.get(addr)

    def get_function_addr_dict(self):
        """Returns dictionary with function address as key for simulation context"""
        ret_dict = {}
        for item in self.functions:
            ret_dict.update({self.functions[item][0]: item})
        return ret_dict

    def get_function_label_dict(self):
        """Returns dictionary with label address as key for simulation context"""
        ret_dict = {}
        for item in self.labels:
            ret_dict.update({self.labels[item]: item})
        return ret_dict

    def get_loop_ranges(self):
        """Returns list with address ranges for each loop"""
        ret_list = []
        for item in self.loopclose:
            ret_list.append(range(item + 1, self.loopclose[item]))
        return ret_list


class InstructionFactory(object):

    def __init__(self):
        # Mapping of mnemonics to instruction classes
        self.mnem_map = {}
        self.opcode_map = {}
        self.__register_mnemonics(Ins)
        self.__register_opcodes(Ins)

    def __register_mnemonics(self, class_p):
        """ Find all final classes derived from Ins and append their mnemonic and class type to dictionary"""
        for cls in class_p.__subclasses__():
            if len(cls.__subclasses__()) > 0:
                self.__register_mnemonics(cls)
            else:
                if isinstance(cls.MNEM, str):
                    if cls.MNEM in self.mnem_map:
                        raise Exception('Error adding mnemonic \'' + cls.MNEM + '\' for class ' + cls.__name__
                                        + '. Mnemonic already in use.')
                    self.mnem_map.update({cls.MNEM: cls})
                elif isinstance(cls.MNEM, dict):
                    for item in cls.MNEM.values():
                        if item in self.mnem_map:
                            raise Exception('Error adding mnemonic \'' + item + '\' for class ' + cls.__name__
                                            + '. Mnemonic already in use.')
                        self.mnem_map.update({item: cls})
                else:
                    raise Exception('Invalid mnemonic format for class ' + cls.__name__)

    def __register_opcodes(self, class_p):
        for cls in class_p.__subclasses__():
            if len(cls.__subclasses__()) > 0:
                self.__register_opcodes(cls)
            else:
                self.opcode_map.update({cls.OP: cls})

    def factory_asm(self, addr, asm_str, ctx):
        """Create instruction class object, based on assembly string"""
        asm_split = asm_str.split(maxsplit=1)
        mnem = asm_split[0].strip()
        params = ''
        if len(asm_split) == 2:
            params = asm_split[1].strip()
        if not self.is_valid_mnem(mnem):
            raise SyntaxError('Unknown instruction: \'' + mnem + '\'')
        ins_obj = self.mnem_map[mnem].from_assembly(addr, mnem, params, ctx)
        return ins_obj

    def factory_bin(self, ins_in, ctx):
        """Create instruction class object. Works for hexstrings or integers"""
        if isinstance(ins_in, str):
            if len(ins_in) == 8:
                ins = int(ins_in, 16)
            else:
                raise ValueError("Wrong length of instruction. Must be 8 hex digits.")
        else:
            ins = ins_in
        op_bits = ins >> Ins.OP_POS
        ins_class = self.opcode_map[op_bits]
        if ins_class:
            return ins_class.from_ins_word(ins, ctx)
        else:
            raise UnknownOpcodeError("Unknown opcode")

    def is_valid_mnem(self, mnem):
        return mnem in self.mnem_map


class Ins(object):
    """Basic instruction with opcode and fun field"""
    INS_LEN = 32
    REG_LEN = 5
    OP_LEN = 6
    FUN_LEN = 3
    LIMB_LEN = 3
    OP_POS = 26
    FUN_POS = 23

    FUN_RANGE = (FUN_POS+FUN_LEN-1, FUN_POS)

    CYCLES = 1

    malformed = False
    fun = 0

    zero_ranges = []

    def __init__(self, ins, ctx):
        self.ins = ins
        self.ctx = ctx
        self.check_zero_ranges()
        self.dec()

    @classmethod
    def from_ins_word(cls, ins, ctx):
        """Create instruction object from binary instruction word"""
        return cls(ins, ctx)

    @classmethod
    def from_assembly(cls, address, mnem, params, ctx):
        """Create instruction object from assembly string"""
        return cls.enc(address, mnem, params, ctx)

    def get_hexstr(self):
        return '0x' + hex(self.ins)[2:].zfill(8)

    def get_bit_slice(self, pos, slice_len):
        if (slice_len + pos) <= self.INS_LEN and pos >= 0:
            return (self.ins >> pos) & (2 ** slice_len - 1)
        else:
            raise ValueError("Invalid slice")

    @staticmethod
    def get_gen_bit_slice(src, pos, slice_len):
        return (src >> pos) & (2 ** slice_len - 1)

    def dec(self):
        self.fun = self.get_bit_slice(self.FUN_POS, self.FUN_LEN)

    def get_byte(self, byte):
        return self.get_bit_slice(byte*8, 8)

    def get_byte_bin_str(self, byte):
        return bin(self.get_byte(byte))[2:].zfill(8)

    def get_bin_with_separators(self):
        return '|' + self.get_byte_bin_str(3) + '|' + self.get_byte_bin_str(2) + '|'\
               + self.get_byte_bin_str(1) + '|' + self.get_byte_bin_str(0) + '|'

    @staticmethod
    def get_enc_table_hdr():
        return '|31    24|23    16|15     8|7      0|'

    def get_reg_at_pos(self, pos):
        if ((self.REG_LEN + pos + self.OP_LEN) <= self.INS_LEN) and pos >= 0:
            return self.get_bit_slice(pos, self.REG_LEN)
        else:
            raise ValueError("Invalid pos for reg")

    def reg_as_limb(self, reg):
        """decode limb encoding in reg field"""
        if reg < 0 or reg >= 2**self.REG_LEN:
            raise ValueError("Invalid register")
        dmem = bool((reg >> 4) & 0b1)
        inc = bool((reg >> 3) & 0b1)
        limb = reg & 0b111
        return dmem, inc, limb

    def check_zero_ranges(self):
        # Get Zero ranges from all super classes
        zero_ranges = []
        for item in self.__class__.mro()[:-1]:
            zero_ranges.extend(item.zero_ranges)
        for i in zero_ranges:
            if i:
                if self.get_bit_slice(i[1], i[0]-i[1]+1):
                    self.malformed = True

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        raise Exception('This method must be overridden in a derived class')

    @staticmethod
    def enc_limb_for_reg(limb, inc, dmem):
        return limb + (int(inc) << 3) + (int(dmem) << 4)

    @classmethod
    def enc_op(cls, op):
        if op < 0 or op >= 2**cls.OP_LEN:
            raise OverflowError('Opcode out of bounds')
        return op << cls.OP_POS

    @classmethod
    def enc_fun(cls, fun):
        if fun < 0 or fun >= 2**cls.FUN_LEN:
            raise OverflowError('Fun field out of bounds')
        return fun << cls.FUN_POS

    @classmethod
    def get_bin_for_mnem(cls, mnem):
        rev_mnem = {v: k for k, v in cls.MNEM.items()}
        if mnem not in rev_mnem:
            raise Exception('Internal error: unexpected mnemonic: ' + mnem)
        return rev_mnem.get(mnem)

    def get_cycles(self):
        return self.CYCLES

    def convert_otbn(self, addr):
        return None


class GIStd(Ins):
    """Standard Format (Rd+Rs2+Rs1+Imm)"""
    IMM_LEN = 8
    IMM_POS = 0
    RD_POS = 18
    RS2_POS = 13
    RS1_POS = 8

    IMM_RANGE = (IMM_POS+IMM_LEN-1, IMM_POS)
    RD_RANGE = (RD_POS+Ins.REG_LEN-1, RD_POS)
    RS1_RANGE = (RS1_POS+Ins.REG_LEN-1, RS1_POS)
    RS2_RANGE = (RS2_POS+Ins.REG_LEN-1, RS2_POS)

    rd = 0
    rs1 = 0
    rs2 = 0
    imm = 0

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        self.rd = self.get_reg_at_pos(self.RD_POS)
        self.rs2 = self.get_reg_at_pos(self.RS2_POS)
        self.rs1 = self.get_reg_at_pos(self.RS1_POS)
        self.imm = self.get_bit_slice(self.IMM_POS, self.IMM_LEN)

    @classmethod
    def enc_imm(cls, imm):
        if imm < 0 or imm >= 2**cls.IMM_LEN:
            raise SyntaxError('Immediate out of bounds')
        return imm << cls.IMM_POS

    @classmethod
    def enc_rd(cls, reg):
        if reg < 0 or reg >= 2**cls.REG_LEN:
            raise OverflowError('reg index out of bounds')
        return reg << cls.RD_POS

    @classmethod
    def enc_rs1(cls, reg):
        if reg < 0 or reg >= 2**cls.REG_LEN:
            raise OverflowError('reg index out of bounds')
        return reg << cls.RS1_POS

    @classmethod
    def enc_rs2(cls, reg):
        if reg < 0 or reg >= 2**cls.REG_LEN:
            raise OverflowError('reg index out of bounds')
        return reg << cls.RS2_POS


class GIStdShift(GIStd):
    """Standard format with immediate shift of RS2"""
    SHIFT_IMM_LEN = 7
    SHIFT_IMM_POS = 0
    SHIFT_DIR_POS = 7
    SHIFT_DIR_LEN = 1
    MAX_SHIFT = 31

    shift_bytes = 0
    shift_right = False

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        self.shift_bytes = self.get_gen_bit_slice(self.imm, self.SHIFT_IMM_POS, self.SHIFT_IMM_LEN)
        self.shift_right = bool(self.get_gen_bit_slice(self.imm, self.SHIFT_DIR_POS, self.SHIFT_DIR_LEN))
        if self.shift_bytes > self.MAX_SHIFT:
            self.malformed = True

    def get_asm_str(self):
        asm_str = self.MNEM.get(self.fun) + ' r' + str(self.rd) + ', r' + str(self.rs1) + ', r' + str(self.rs2)
        if self.shift_right:
            asm_str += ' >> ' + str(self.shift_bytes*8)
        else:
            if self.shift_bytes:
                asm_str += ' << ' + str(self.shift_bytes*8)
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        enc_tab += '|< op ><0|><rd ><r|s2><rs1>|D<shift>|\n'
        enc_tab += 'D=0: left shift; D=1: right shift'
        return enc_tab

    @classmethod
    def enc_shift(cls, shift_bytes, shift_right):
        ret = 0
        ret += int(shift_right) << 7
        if shift_bytes < 0 or shift_bytes > cls.MAX_SHIFT:
            raise OverflowError('Syntax error: shift immediate out of bounds')
        ret += shift_bytes
        return ret

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        ret = 0
        if cls.SINGLE_INPUT:
            rd, rs, shift_right, shift_bits = _get_two_regs_with_shift(params)
            ret += cls.enc_rs2(rs)
        else:
            rd, rs1, rs2, shift_right, shift_bits = _get_three_regs_with_shift(params)
            ret += cls.enc_rs1(rs1)
            ret += cls.enc_rs2(rs2)
        if shift_bits % 8:
            raise SyntaxError('Input shift immediate not byte aligned')
        ret += cls.enc_shift(int(shift_bits / 8), shift_right)
        ret += cls.enc_rd(rd)
        ret += cls.enc_op(cls.OP)
        ret += cls.enc_fun(cls.get_bin_for_mnem(mnem))
        return cls(ret, ctx.ins_ctx)


class GIStdNoParm(GIStd):
    """Generic Instruction with no parameters"""
    zero_ranges = [Ins.FUN_RANGE, GIStd.RD_RANGE, GIStd.RS2_RANGE, GIStd.RS1_RANGE, GIStd.IMM_RANGE]

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def get_asm_str(self):
        asm_str = self.MNEM.get(self.fun)
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        enc_tab += '|< op ><         0                 >|'
        return enc_tab


class GIWideImm(Ins):
    """Wide Immediate Format (Rd+Funi+Imm)"""
    IMM_LEN = 16
    IMM_POS = 0
    RD_POS = 18
    FUNI_POS = 16
    FUNI_LEN = 2

    IMM_RANGE = (IMM_POS+IMM_LEN-1, IMM_POS)
    RD_RANGE = (RD_POS+Ins.REG_LEN-1, RD_POS)
    FUNI_RANGE = (FUNI_POS+FUNI_LEN-1, FUNI_POS)

    zero_ranges = []

    rd = 0
    funi = 0
    imm = 0

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        self.rd = self.get_reg_at_pos(self.RD_POS)
        self.funi = self.get_bit_slice(self.FUNI_POS, self.FUNI_LEN)
        self.imm = self.get_bit_slice(self.IMM_POS, self.IMM_LEN)

    @classmethod
    def enc_imm(cls, imm):
        if imm < 0 or imm >= 2**cls.IMM_LEN:
            raise SyntaxError('Immediate out of bounds')
        return imm << cls.IMM_POS

    @classmethod
    def enc_rd(cls, reg):
        if reg < 0 or reg >= 2**cls.REG_LEN:
            raise OverflowError('reg index out of bounds')
        return reg << cls.RD_POS

    @classmethod
    def enc_funi(cls, funi):
        if funi < 0 or funi >= 2**GIWideImm.FUNI_LEN:
            raise OverflowError('reg index out of bounds')
        return funi << cls.FUNI_POS


class GIMidImm(Ins):
    """ Mid Immediate Format (funb+Imm)"""
    IMM_LEN = 12
    IMM_POS = 0
    FUNB_POS = 12
    FUNB_LEN = 11

    IMM_RANGE = (IMM_POS+IMM_LEN-1, IMM_POS)
    FUNB_RANGE = (FUNB_POS+FUNB_LEN-1, FUNB_POS)

    zero_ranges = []

    funb = 0
    imm = 0

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        self.funb = self.get_bit_slice(self.FUNB_POS, self.FUNB_LEN)
        self.imm = self.get_bit_slice(self.IMM_POS, self.IMM_LEN)

    @classmethod
    def enc_imm(cls, imm):
        if imm < 0 or imm >= 2**cls.IMM_LEN:
            raise SyntaxError('Immediate out of bounds')
        return imm << cls.IMM_POS

    @classmethod
    def enc_funb(cls, funb):
        if funb < 0 or funb >= 2**GIMidImm.FUNB_LEN:
            raise OverflowError('funb index out of bounds')
        return funb << cls.FUNB_POS


#############################################
#              Arithmetic                   #
#############################################

class IAdd(GIStdShift):
    """Add instructions with one shifted input"""

    # addi is not a shift instruction but also treated here since same opcode
    MNEM = {0b000: 'add', 0b001: 'addc', 0b010: 'addi', 0b100: 'addx', 0b101: 'addcx'}
    OP = 0b010100

    # ugly hack to allow special treatment for addi (prevent overflow detection for shift imm value)
    MAX_SHIFT = 255

    # this is used in case for shift format only, where all instructions are dual input. Addi is treated separately
    SINGLE_INPUT = 0

    zero_ranges = []

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        # test again with real max value if shit immediate is in bounds, since we deactivated it earlier
        if self.MNEM.get(self.fun) != 'addi':
            self.MAX_SHIFT = super().MAX_SHIFT
            if self.shift_bytes > self.MAX_SHIFT:
                self.malformed = True

    def get_asm_str(self):
        if self.MNEM.get(self.fun) == 'addi':
            asm_str = self.MNEM.get(self.fun) + ' r' + str(self.rd) + ', r' + str(self.rs1) + ', #' + str(self.imm)
            return self.get_hexstr(), asm_str, self.malformed
        else:
            return super().get_asm_str()

    def get_enc_tab(self):
        if self.MNEM.get(self.fun) == 'addi':
            enc_tab = self.get_enc_table_hdr() + '\n'
            enc_tab += self.get_bin_with_separators() + '\n'
            enc_tab += '|< op ><0|><rd ><r|s2><rs1>|<  imm >|'
            return enc_tab
        else:
            return super().get_enc_tab()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        if mnem == 'addi':
            ret = 0
            rd, rs, imm = _get_double_reg_with_imm(params)
            ret += cls.enc_rd(rd)
            ret += cls.enc_rs1(rs)
            ret += cls.enc_imm(imm)
            ret += cls.enc_fun(cls.get_bin_for_mnem(mnem))
            ret += cls.enc_op(cls.OP)
            return cls(ret, ctx.ins_ctx)
        else:
            return super().enc(addr, mnem, params, ctx)

    def convert_otbn(self, addr):
        if self.shift_right:
            shift_type = 'right'
        else:
            shift_type = 'left'
        if self.MNEM.get(self.fun) == 'add':
            return [IBnAdd(self.rd, self.rs1, self.rs2, 'standard', shift_type, self.shift_bytes, self.ctx)]
        if self.MNEM.get(self.fun) == 'addx':
            return [IBnAdd(self.rd, self.rs1, self.rs2, 'extension', shift_type, self.shift_bytes, self.ctx)]
        if self.MNEM.get(self.fun) == 'addc':
            return [IBnAddc(self.rd, self.rs1, self.rs2, 'standard', shift_type, self.shift_bytes, self.ctx)]
        if self.MNEM.get(self.fun) == 'addcx':
            return [IBnAddc(self.rd, self.rs1, self.rs2, 'extension', shift_type, self.shift_bytes, self.ctx)]
        if self.MNEM.get(self.fun) == 'addi':
            return [IBnAddi(self.rd, self.rs1, self.imm, 'standard', self.ctx)]
        if self.MNEM.get(self.fun) == 'addix':
            return [IBnAddi(self.rd, self.rs1, self.imm, 'extension', self.ctx)]
        return None

    def execute(self, m):
        if self.MNEM.get(self.fun) != 'addi':
            if self.shift_right:
                rs2op = (m.get_reg(self.rs2) >> self.shift_bytes*8) & m.xlen_mask
            else:
                rs2op = (m.get_reg(self.rs2) << self.shift_bytes*8) & m.xlen_mask
        if self.MNEM.get(self.fun) == 'add':
            res = m.get_reg(self.rs1) + rs2op
            m.stat_record_flag_access('n', self.MNEM.get(self.fun))
            m.set_c_z_m_l(res)
        elif self.MNEM.get(self.fun) == 'addc':
            res = m.get_reg(self.rs1) + rs2op + int(m.get_flag('C'))
            m.stat_record_flag_access('n', self.MNEM.get(self.fun))
            m.set_c_z_m_l(res)
        elif self.MNEM.get(self.fun) == 'addi':
            res = m.get_reg(self.rs1) + self.imm
            m.stat_record_flag_access('n', self.MNEM.get(self.fun))
            m.set_c_z_m_l(res)
        elif self.MNEM.get(self.fun) == 'addx':
            res = m.get_reg(self.rs1) + rs2op + int(m.get_flag('C'))
            m.stat_record_flag_access('x', self.MNEM.get(self.fun))
            m.setx_c_z_m_l(res)
        elif self.MNEM.get(self.fun) == 'addcx':
            res = m.get_reg(self.rs1) + rs2op + int(m.get_flag('XC'))
            m.stat_record_flag_access('x', self.MNEM.get(self.fun))
            m.setx_c_z_m_l(res)
        else:
            raise Exception('Invalid opcode')
        m.set_reg(self.rd, res & m.xlen_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IAddm(GIStdShift):
    """'addm' instruction"""
    MNEM = {0b000: 'addm'}
    OP = 0b100111

    SINGLE_INPUT = 0

    zero_ranges = []

    def convert_otbn(self, addr):
        return [IBnAddm(self.rd, self.rs1, self.rs2, self.ctx)]

    def execute(self, m):
        if self.shift_right:
            rs2op = (m.get_reg(self.rs2) >> self.shift_bytes*8) & m.xlen_mask
        else:
            rs2op = (m.get_reg(self.rs2) << self.shift_bytes*8) & m.xlen_mask
        res = (m.get_reg(self.rs1) + rs2op) % m.get_reg('mod')
        m.set_z_m_l(res)
        m.set_reg(self.rd, res)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class ISub(GIStdShift):
    """Sub instructions (with one shifted input)"""

    # subi is not a shift instruction but also treated here since same opcode
    MNEM = {0b000: 'sub', 0b001: 'subb', 0b010: 'subi', 0b100: 'subx', 0b101: 'subbx'}
    OP = 0b010101

    # ugly hack to allow special treatment for subi (prevent overflow detection for shift imm value)
    MAX_SHIFT = 255

    # this is used in case for shift format only, where all instructions are dual input. subi is treated separately
    SINGLE_INPUT = 0

    zero_ranges = []

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        # test again with real max value if shit immediate is in bounds, since we deactivated it earlier
        if self.MNEM.get(self.fun) != 'subi':
            self.MAX_SHIFT = super().MAX_SHIFT
            if self.shift_bytes > self.MAX_SHIFT:
                self.malformed = True

    def get_asm_str(self):
        if self.MNEM.get(self.fun) == 'subi':
            asm_str = self.MNEM.get(self.fun) + ' r' + str(self.rd) + ', r' + str(self.rs1) + ', #' + str(self.imm)
            return self.get_hexstr(), asm_str, self.malformed
        else:
            return super().get_asm_str()

    def get_enc_tab(self):
        if self.MNEM.get(self.fun) == 'subi':
            enc_tab = self.get_enc_table_hdr() + '\n'
            enc_tab += self.get_bin_with_separators() + '\n'
            enc_tab += '|< op ><0|><rd ><r|s2><rs1>|<  imm >|'
            return enc_tab
        else:
            return super().get_enc_tab()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        if mnem == 'subi':
            ret = 0
            rd, rs, imm = _get_double_reg_with_imm(params)
            ret += cls.enc_rd(rd)
            ret += cls.enc_rs1(rs)
            ret += cls.enc_imm(imm)
            ret += cls.enc_fun(cls.get_bin_for_mnem(mnem))
            ret += cls.enc_op(cls.OP)
            return cls(ret, ctx.ins_ctx)
        else:
            return super().enc(addr, mnem, params, ctx)

    def convert_otbn(self, addr):
        if self.shift_right:
            shift_type = 'right'
        else:
            shift_type = 'left'
        if self.MNEM.get(self.fun) == 'sub':
            return [IBnSub(self.rd, self.rs1, self.rs2, 'standard', shift_type, self.shift_bytes, self.ctx)]
        if self.MNEM.get(self.fun) == 'subx':
            return [IBnSub(self.rd, self.rs1, self.rs2, 'extension', shift_type, self.shift_bytes, self.ctx)]
        if self.MNEM.get(self.fun) == 'subb':
            return [IBnSubb(self.rd, self.rs1, self.rs2, 'standard', shift_type, self.shift_bytes, self.ctx)]
        if self.MNEM.get(self.fun) == 'subbx':
            return [IBnSubb(self.rd, self.rs1, self.rs2, 'extension', shift_type, self.shift_bytes, self.ctx)]
        if self.MNEM.get(self.fun) == 'subi':
            return [IBnSubi(self.rd, self.rs1, self.imm, 'standard', self.ctx)]
        if self.MNEM.get(self.fun) == 'subix':
            return [IBnSubi(self.rd, self.rs1, self.imm, 'extension', self.ctx)]
        return None

    def execute(self, m):
        if self.MNEM.get(self.fun) != 'subi':
            if self.shift_right:
                rs2op = (m.get_reg(self.rs2) >> self.shift_bytes*8) & m.xlen_mask
            else:
                rs2op = (m.get_reg(self.rs2) << self.shift_bytes*8) & m.xlen_mask
        b = m.get_reg(self.rs2) > m.get_reg(self.rs1)
        if self.MNEM.get(self.fun) == 'sub':
            res = m.get_reg(self.rs1) - rs2op
            m.set_flag('C', b)
            m.stat_record_flag_access('n', self.MNEM.get(self.fun))
            m.set_z_m_l(res & m.xlen_mask)
        elif self.MNEM.get(self.fun) == 'subb':
            res = m.get_reg(self.rs1) - rs2op - int(m.get_flag('C'))
            m.set_flag('C', b)
            m.stat_record_flag_access('n', self.MNEM.get(self.fun))
            m.set_z_m_l(res & m.xlen_mask)
        elif self.MNEM.get(self.fun) == 'subi':
            res = m.get_reg(self.rs1) - self.imm
            m.set_flag('C', b)
            m.stat_record_flag_access('n', self.MNEM.get(self.fun))
            m.set_z_m_l(res & m.xlen_mask)
        elif self.MNEM.get(self.fun) == 'subx':
            res = m.get_reg(self.rs1) - rs2op
            m.set_flag('XC', b)
            m.stat_record_flag_access('x', self.MNEM.get(self.fun))
            m.setx_z_m_l(res & m.xlen_mask)
        elif self.MNEM.get(self.fun) == 'subbx':
            res = m.get_reg(self.rs1) - rs2op - int(m.get_flag('XC'))
            m.set_flag('XC', b)
            m.stat_record_flag_access('x', self.MNEM.get(self.fun))
            m.setx_z_m_l(res & m.xlen_mask)
        else:
            raise Exception('Invalid opcode')
        m.set_reg(self.rd, res & m.xlen_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class ISubm(GIStdShift):
    """Mod subtraction"""
    MNEM = {0b000: 'subm'}
    OP = 0b101000

    SINGLE_INPUT = 0

    zero_ranges = [(7, 0)]  # disallow shifting for now

    def convert_otbn(self, addr):
        return [IBnSubm(self.rd, self.rs1, self.rs2, self.ctx)]

    def execute(self, m):
        if self.shift_right:
            rs2op = (m.get_reg(self.rs2) >> self.shift_bytes*8) & m.xlen_mask
        else:
            rs2op = (m.get_reg(self.rs2) << self.shift_bytes*8) & m.xlen_mask
        res = (m.get_reg(self.rs1) - rs2op) % m.get_reg('mod')
        m.set_z_m_l(res & m.xlen_mask)
        m.set_reg(self.rd, res & m.xlen_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IMul128(GIStd):
    """Multiplication"""
    zero_ranges = [(7, 0)]
    MNEM = 'mul128'
    R1UL_POS = 0
    R1UL_LEN = 1
    R2UL_POS = 1
    R2UL_LEN = 1
    OP = 0b010110

    CYCLES = 4

    r1_upper = 0
    r2_upper = 0

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        self.r1_upper = bool(self.get_gen_bit_slice(self.fun, self.R1UL_POS, self.R1UL_LEN))
        self.r2_upper = bool(self.get_gen_bit_slice(self.fun, self.R2UL_POS, self.R2UL_LEN))

    def get_asm_str(self):
        asm_str = self.MNEM + ' r' + str(self.rd) + ', r' + str(self.rs1)
        if self.r1_upper:
            asm_str += 'u'
        else:
            asm_str += 'l'
        asm_str += ', r' + str(self.rs2)
        if self.r2_upper:
            asm_str += 'u'
        else:
            asm_str += 'l'
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        enc_tab += '|< op ><0|><rd ><r|s2><rs1>|< shift>|'
        return enc_tab

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        ret = 0
        rd, rs1, rs1upper, rs2, rs2upper = _get_three_regs_with_sections(params)
        fun = (int(rs1upper) << cls.R1UL_POS) + (int(rs2upper) << cls.R2UL_POS)
        ret += cls.enc_rd(rd)
        ret += cls.enc_rs1(rs1)
        ret += cls.enc_rs2(rs2)
        ret += cls.enc_fun(fun)
        ret += cls.enc_op(cls.OP)
        return cls(ret, ctx.ins_ctx)

    def convert_otbn(self, addr):
        rs1_hw_sel = 'upper' if self.r1_upper else'lower'
        rs2_hw_sel = 'upper' if self.r2_upper else 'lower'
        return [IBnMulh(self.rd, self.rs1, rs1_hw_sel, self.rs2, rs2_hw_sel, self.ctx)]

    def execute(self, m):
        op1 = (m.get_reg(self.rs1) >> int(m.XLEN/2)*int(self.r1_upper)) & m.half_xlen_mask
        op2 = (m.get_reg(self.rs2) >> int(m.XLEN/2)*int(self.r2_upper)) & m.half_xlen_mask
        res = op1*op2
        m.set_reg(self.rd, res)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


#############################################
#      Logical, select, shift, compare      #
#############################################

class IAnd(GIStdShift):
    """Bitwise and with input shift"""
    MNEM = {0b000: 'and'}  # matched with fun field
    OP = 0b010000
    SINGLE_INPUT = False

    zero_ranges = []

    def convert_otbn(self, addr):
        if self.shift_right:
            shift_type = 'right'
        else:
            shift_type = 'left'
        return [IBnAnd(self.rd, self.rs1, self.rs2, 'standard', shift_type, self.shift_bytes, self.ctx)]

    def execute(self, m):
        if self.shift_right:
            rs2op = (m.get_reg(self.rs2) >> self.shift_bytes*8) & m.xlen_mask
        else:
            rs2op = (m.get_reg(self.rs2) << self.shift_bytes*8) & m.xlen_mask
        res = m.get_reg(self.rs1) & rs2op
        m.set_z_m_l(res)
        m.set_reg(self.rd, res)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOr(GIStdShift):
    """Bitwise or with input shift"""
    MNEM = {0b000: 'or'}  # matched with fun field
    OP = 0b010001
    SINGLE_INPUT = False

    zero_ranges = []

    def convert_otbn(self, addr):
        if self.shift_right:
            shift_type = 'right'
        else:
            shift_type = 'left'
        return [IBnOr(self.rd, self.rs1, self.rs2, 'standard', shift_type, self.shift_bytes, self.ctx)]

    def execute(self, m):
        if self.shift_right:
            rs2op = (m.get_reg(self.rs2) >> self.shift_bytes*8) & m.xlen_mask
        else:
            rs2op = (m.get_reg(self.rs2) << self.shift_bytes*8) & m.xlen_mask
        res = m.get_reg(self.rs1) | rs2op
        m.set_z_m_l(res)
        m.set_reg(self.rd, res)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class INot(GIStdShift):
    """Bitwise and + shift (incomplete, encoding of shift unclear)"""
    MNEM = {0b000: 'not'}  # matched with fun field
    OP = 0b010010
    SINGLE_INPUT = True

    zero_ranges = [GIStd.RS1_RANGE]

    def get_asm_str(self):
        rs = self.rs2
        asm_str = self.MNEM.get(self.fun) + ' r' + str(self.rd) + ', r' + str(rs)
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        enc_tab += '|< op ><0|><rd ><r|s2>< 0 >|D<shift>|\n'
        enc_tab += 'D=0: left shift; D=1: right shift'
        return enc_tab

    def convert_otbn(self, addr):
        if self.shift_right:
            shift_type = 'right'
        else:
            shift_type = 'left'
        return [IBnNot(self.rd, self.rs2, shift_type, self.shift_bytes, self.ctx)]

    def execute(self, m):
        if self.shift_right:
            rsop = (m.get_reg(self.rs2) >> self.shift_bytes*8) & m.xlen_mask
        else:
            rsop = (m.get_reg(self.rs2) << self.shift_bytes*8) & m.xlen_mask
        res = ~rsop & m.xlen_mask
        m.set_z_m_l(res)
        m.set_reg(self.rd, res)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IXor(GIStdShift):
    """Bitwise XOR with input shift"""
    MNEM = {0: 'xor'}
    OP = 0b010011
    SINGLE_INPUT = False

    zero_ranges = []

    def convert_otbn(self, addr):
        if self.shift_right:
            shift_type = 'right'
        else:
            shift_type = 'left'
        return [IBnXor(self.rd, self.rs1, self.rs2, 'standard', shift_type, self.shift_bytes, self.ctx)]


    def execute(self, m):
        if self.shift_right:
            rs2op = (m.get_reg(self.rs2) >> self.shift_bytes*8) & m.xlen_mask
        else:
            rs2op = (m.get_reg(self.rs2) << self.shift_bytes*8) & m.xlen_mask
        res = m.get_reg(self.rs1) ^ rs2op
        m.set_z_m_l(res & m.xlen_mask)
        m.set_reg(self.rd, res & m.xlen_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class ISel(GIStd):
    """Select Instruction (Function encoded in op2 and imm)"""
    MNEM = {  # matched tuple of (fun, imm)
        # fun   # imm
        (0b000, 0b00000001): 'sell',
        (0b000, 0b00000010): 'selm',
        (0b000, 0b00001000): 'selc',
        (0b100, 0b00000001): 'sellx',
        (0b100, 0b00001000): 'selcx'}
    OP = 0b011001

    zero_ranges = []

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def get_asm_str(self):
        asm_str = self.MNEM.get((self.fun, self.imm)) + ' r' + str(self.rd) + ', r'\
                  + str(self.rs1) + ', r' + str(self.rs2)
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        enc_tab += '|< op ><f|><rd ><r|s2><rs1>|<   f  >|'
        return enc_tab

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        ret = 0
        fun_imm = cls.get_bin_for_mnem(mnem)
        ret += cls.enc_fun(fun_imm[0])
        ret += cls.enc_imm(fun_imm[1])
        rd, rs1, rs2 = _get_triple_reg(params)
        ret += cls.enc_rd(rd)
        ret += cls.enc_rs1(rs1)
        ret += cls.enc_rs2(rs2)
        ret += cls.enc_op(cls.OP)
        return cls(ret, ctx.ins_ctx)

    def convert_otbn(self, addr):
        if self.MNEM.get((self.fun, self.imm)) == 'sell':
            return [IBnSel(self.rd, self.rs1, self.rs2, 'standard', 'l', self.ctx)]
        if self.MNEM.get((self.fun, self.imm)) == 'selm':
            return [IBnSel(self.rd, self.rs1, self.rs2, 'standard', 'm', self.ctx)]
        if self.MNEM.get((self.fun, self.imm)) == 'selc':
            return [IBnSel(self.rd, self.rs1, self.rs2, 'standard', 'c', self.ctx)]
        if self.MNEM.get((self.fun, self.imm)) == 'selz':
            return [IBnSel(self.rd, self.rs1, self.rs2, 'standard', 'z', self.ctx)]
        if self.MNEM.get((self.fun, self.imm)) == 'sellx':
            return [IBnSel(self.rd, self.rs1, self.rs2, 'extension', 'l', self.ctx)]
        if self.MNEM.get((self.fun, self.imm)) == 'selmx':
            return [IBnSel(self.rd, self.rs1, self.rs2, 'extension', 'm', self.ctx)]
        if self.MNEM.get((self.fun, self.imm)) == 'selcx':
            return [IBnSel(self.rd, self.rs1, self.rs2, 'extension', 'c', self.ctx)]
        if self.MNEM.get((self.fun, self.imm)) == 'selzx':
            return [IBnSel(self.rd, self.rs1, self.rs2, 'extension', 'z', self.ctx)]
        return None

    def execute(self, m):
        if self.MNEM.get((self.fun, self.imm)) == 'sell':
            sel = m.get_flag('L')
        elif self.MNEM.get((self.fun, self.imm)) == 'selm':
            sel = m.get_flag('M')
        elif self.MNEM.get((self.fun, self.imm)) == 'selc':
            sel = m.get_flag('C')
        elif self.MNEM.get((self.fun, self.imm)) == 'sellx':
            sel = m.get_flag('XL')
        elif self.MNEM.get((self.fun, self.imm)) == 'selcx':
            sel = m.get_flag('XC')
        else:
            raise Exception('Invalid opcode')
        if sel:
            m.set_reg(self.rd, m.get_reg(self.rs1))
        else:
            m.set_reg(self.rd, m.get_reg(self.rs2))

        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IRshi(GIStd):
    """Concatenate and right shift"""
    MNEM = {0: 'rshi'}
    OP = 0b011010
    MA_SHIFT = 255

    zero_ranges = []

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def get_asm_str(self):
        asm_str = self.MNEM.get(self.fun) + ' r' + str(self.rd) + ', r' + str(self.rs1) + ', r' + str(self.rs2)
        asm_str += ' >> ' + str(self.imm)
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        enc_tab += '|< op ><0|><rd ><r|s2><rs1>|< shift>|'
        return enc_tab

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        ret = 0
        rd, rs1, rs2, shift_right, shift_bits = _get_three_regs_with_shift(params)
        ret += cls.enc_rd(rd)
        ret += cls.enc_rs1(rs1)
        ret += cls.enc_rs2(rs2)
        if not shift_right:
            raise SyntaxError('Only right shifting allowed with rshi instruction')
        if shift_bits < 0 or shift_bits > cls.MA_SHIFT:
            raise SyntaxError('Shift immediate out of bounds')
        ret += cls.enc_imm(shift_bits)
        ret += cls.enc_op(cls.OP)
        ret += cls.enc_fun(cls.get_bin_for_mnem(mnem))
        return cls(ret, ctx.ins_ctx)

    def convert_otbn(self, addr):
        return [IBnRshi(self.rd, self.rs1, self.rs2, self.imm, self.ctx)]

    def execute(self, m):
        conc = (m.get_reg(self.rs2) << m.XLEN) + m.get_reg(self.rs1)
        res = (conc >> self.imm) & m.xlen_mask
        m.set_reg(self.rd, res)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class ICmp(GIStd):
    """Compare Instructions (2rs)"""
    MNEM = {0: 'cmp', 5: 'cmpbx'}
    OP = 0b010111

    zero_ranges = [GIStd.RD_RANGE, GIStd.IMM_RANGE]

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def get_asm_str(self):
        asm_str = self.MNEM.get(self.fun) + ' r' + str(self.rs1) + ', r' + str(self.rs2)
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        enc_tab += '|< op ><0|>< 0 ><r|s2><rs1>|<  0   >|'
        return enc_tab

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        ret = 0
        rs1, rs2 = _get_double_reg(params)
        ret += cls.enc_rs1(rs1)
        ret += cls.enc_rs2(rs2)
        ret += cls.enc_op(cls.OP)
        ret += cls.enc_fun(cls.get_bin_for_mnem(mnem))
        return cls(ret, ctx.ins_ctx)

    def convert_otbn(self, addr):
        if self.MNEM.get(self.fun) == 'cmp':
            return [IBnCmp(self.rs1, self.rs2, 'standard', 'left', 0, self.ctx)]
        if self.MNEM.get(self.fun) == 'cmpx':
            return [IBnCmp(self.rs1, self.rs2, 'extension', 'left', 0, self.ctx)]
        if self.MNEM.get(self.fun) == 'cmpb':
            return [IBnCmpb(self.rs1, self.rs2, 'standard', 'left', 0, self.ctx)]
        if self.MNEM.get(self.fun) == 'cmpbx':
            return [IBnCmpb(self.rs1, self.rs2, 'extension', 'left', 0, self.ctx)]
        return None

    def execute(self, m):
        if self.MNEM.get(self.fun) == 'cmp':
            m.stat_record_flag_access('n', self.MNEM.get(self.fun))
            if m.get_reg(self.rs2) == m.get_reg(self.rs1):
                m.set_flag('Z', True)
            else:
                m.set_flag('Z', False)
            if m.get_reg(self.rs2) > m.get_reg(self.rs1):
                m.set_flag('C', True)
            else:
                m.set_flag('C', False)
        elif self.MNEM.get(self.fun) == 'cmpbx':
            m.stat_record_flag_access('x', self.MNEM.get(self.fun))
            if m.get_reg(self.rs2) > m.get_reg(self.rs1):
                m.set_flag('XC', True)
            if m.get_reg(self.rs2) < m.get_reg(self.rs1):
                m.set_flag('XC', False)
            # if rs1 and rs2 are equal XC is left unchanged
        else:
            raise Exception('Invalid opcode')

        trace_str = self.get_asm_str()[1]
        return trace_str, None


#############################################
#            Load/Store/Move                #
#############################################

class ILdSt1(GIStd):
    """ Special register Load/Store 1"""
    MNEM = {0b111: 'ldrfp', 0b001: 'ldlc', 0b010: 'stdmp', 0b011: 'lddmp', 0b101: 'lddrp'}
    OP = 0b100101

    zero_ranges = [GIStd.RS2_RANGE, GIStd.IMM_RANGE]

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        if self.MNEM.get(self.fun) == 'stdmp':
            if self.rs1:
                self.malformed = True  # rs1 must be zero for stores
        else:
            if self.rd:
                self.malformed = True  # rd must be zero for stores

    def get_asm_str(self):
        if self.MNEM.get(self.fun) == 'stdmp':
            asm_str = self.MNEM.get(self.fun) + ' r' + str(self.rd)
        else:
            asm_str = self.MNEM.get(self.fun) + ' r' + str(self.rs1)
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        if self.MNEM.get(self.fun) == 'stdmp':
            enc_tab += '|< op ><f|><rd >< |      0 |       >|'
        else:
            enc_tab += '|< op ><f|><   0  |  ><rs1>|<   0  >|'
        return enc_tab

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        ret = 0
        r = _get_single_reg(params)
        if r < 0 or r >= 2**cls.REG_LEN:
            raise OverflowError('Reg index out of bounds')
        if mnem.startswith('ld'):
            ret += GIStd.enc_rs1(r)
        elif mnem.startswith('st'):
            ret += GIStd.enc_rd(r)
        else:
            raise Exception('Internal error: Unexpected mnemonic')
        ret += cls.enc_op(cls.OP)
        ret += cls.enc_fun(cls.get_bin_for_mnem(mnem))
        return cls(ret, ctx.ins_ctx)

    def execute(self, m):
        if self.MNEM.get(self.fun) == 'ldrfp':
            m.set_reg('rfp', m.get_reg(self.rs1))
        elif self.MNEM.get(self.fun) == 'ldlc':
            m.set_reg('lc', m.get_reg(self.rs1))
        elif self.MNEM.get(self.fun) == 'lddmp':
            m.set_reg('dmp', m.get_reg(self.rs1))
        elif self.MNEM.get(self.fun) == 'lddrp':
            m.set_reg('drp', m.get_reg(self.rs1))
        elif self.MNEM.get(self.fun) == 'stdmp':
            m.set_reg(self.rd, m.get_reg('dmp'))
        else:
            raise Exception('Invalid opcode')
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class ILdSt2(GIStd):
    """Special register Load/Store 2"""
    MNEM = {0: 'stmod', 1: 'ldmod', 2: 'strnd', 3: 'ldrnd'}
    OP = 0b100110

    zero_ranges = [GIStd.RS2_RANGE, GIStd.IMM_RANGE]

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        if self.MNEM.get(self.fun).startswith('st'):
            if self.rs1:
                self.malformed = True  # rs1 must be zero for stores
        else:
            if self.rd:
                self.malformed = True  # rd must be zero for stores

    def get_asm_str(self):
        asm_str = self.MNEM.get(self.fun)
        if self.MNEM.get(self.fun).startswith('st'):
            asm_str += ' r' + str(self.rd)
        else:
            asm_str += ' r' + str(self.rs1)
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        if self.MNEM.get(self.fun).startswith('st'):
            enc_tab += '|< op ><o2>< rd><       0          >|'
        else:
            enc_tab += '|< op ><f|><   0  |  ><rs1>|<   0  >|'
        return enc_tab

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        ret = 0
        r = _get_single_reg(params)
        if r < 0 or r >= 2**cls.REG_LEN:
            raise OverflowError('Reg index out of bounds')
        if mnem.startswith('ld'):
            ret += GIStd.enc_rs1(r)
        elif mnem.startswith('st'):
            ret += GIStd.enc_rd(r)
        else:
            raise Exception('Internal error: Unexpected mnemonic')
        ret += cls.enc_op(cls.OP)
        ret += cls.enc_fun(cls.get_bin_for_mnem(mnem))
        return cls(ret, ctx.ins_ctx)

    def convert_otbn(self, addr):
        if self.MNEM.get(self.fun) == 'strnd':
            return [IBnWsrrw(self.rd, 1, self.rd, self.ctx)]
        return None

    def execute(self, m):
        if self.MNEM.get(self.fun) == 'ldmod':
            m.set_reg('mod', m.get_reg(self.rs1))
        elif self.MNEM.get(self.fun) == 'ldrnd':
            m.set_reg('rnd', m.get_reg(self.rs1))
        elif self.MNEM.get(self.fun) == 'stmod':
            m.set_reg(self.rd, m.get_reg('mod'))
        elif self.MNEM.get(self.fun) == 'strnd':
            m.set_reg(self.rd, m.get_reg('rnd'))
        else:
            raise Exception('Invalid opcode')
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class ILdi(GIWideImm):
    """Load from immediate dmem addr"""
    IDX_POS = 5
    IDX_LEN = 9
    zero_ranges = [Ins.FUN_RANGE, GIWideImm.FUNI_RANGE, (4, 0)]

    MNEM = 'ldi'
    OP = 0b100001

    idx = 0

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        self.idx = self.get_gen_bit_slice(self.imm, self.IDX_POS, self.IDX_LEN)
        if self.imm >> 14 != 0b01:
            self.malformed = True  # address must include dmem offset at 0x4000

    def get_asm_str(self):
        asm_str = self.MNEM + ' r' + str(self.rd) + ', [#' + str(self.idx) + ']'
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        enc_tab += '|< op ><0|><rd ><0|>1< addr|  >< 0 >|'
        return enc_tab

    @classmethod
    def enc_idx(cls, idx):
        imm = 0
        imm += 0b01 << 14
        imm += idx << 5
        return cls.enc_imm(imm)

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        ret = 0
        reg, idx = _get_single_reg_and_index_imm(params)
        if reg < 0 or reg >= 2**cls.REG_LEN:
            raise OverflowError('Reg index out of bounds')
        if idx < 0 or idx >= 2**cls.IDX_LEN:
            raise OverflowError('Index out of bounds')
        ret += cls.enc_op(cls.OP)
        ret += cls.enc_fun(0)
        ret += cls.enc_funi(0)
        ret += cls.enc_rd(reg)
        ret += cls.enc_idx(idx)
        return cls(ret, ctx.ins_ctx)

    def convert_otbn(self, addr):
        dmem_mult = 32 if self.ctx.dmem_byte_addressing else 1
        return [IOtAddi(3, 0, self.rd, self.ctx), IBnLid(3, 0, 0, 0, self.idx*dmem_mult, self.ctx)]

    def execute(self, m):
        m.set_reg(self.rd, m.get_dmem(self.idx))
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class ISti(GIWideImm):
    """Store to immediate dmem addr"""
    IDX_POS = 5
    IDX_LEN = 9
    zero_ranges = [Ins.FUN_RANGE, GIWideImm.FUNI_RANGE, (4, 0)]

    MNEM = 'sti'
    OP = 0b100010

    idx = 0

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        self.idx = self.get_gen_bit_slice(self.imm, self.IDX_POS, self.IDX_LEN)
        if self.imm >> 14 != 0b01:
            self.malformed = True  # address must include dmem offset at 0x4000

    def get_asm_str(self):
        asm_str = self.MNEM + ' r' + str(self.rd) + ', [#' + str(self.idx) + ']'
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        enc_tab += '|< op ><0|><rs ><0|>1< addr|  >< 0 >|'
        return enc_tab

    @classmethod
    def enc_idx(cls, idx):
        imm = 0
        imm += 0b01 << 14
        imm += idx << 5
        return cls.enc_imm(imm)

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        ret = 0
        reg, idx = _get_single_reg_and_index_imm(params)
        if reg < 0 or reg >= 2**cls.REG_LEN:
            raise OverflowError('Reg index out of bounds')
        if idx < 0 or idx >= 2**cls.IDX_LEN:
            raise OverflowError('Index out of bounds')
        ret += cls.enc_op(cls.OP)
        ret += cls.enc_fun(0)
        ret += cls.enc_funi(0)
        ret += cls.enc_rd(reg)
        ret += cls.enc_idx(idx)
        return cls(ret, ctx.ins_ctx)

    def execute(self, m):
        m.set_dmem(self.idx, m.get_reg(self.rd))
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IMovLdr(GIStd):
    """Move and ldr"""
    MNEM = {0: 'mov', 1: 'ldr'}
    OP = 0b011111

    zero_ranges = [GIStd.RS2_RANGE, GIStd.IMM_RANGE]

    rs = 0
    rs_dmem = 0
    rs_inc = 0
    rs_limb = 0
    rd_dmem = 0
    rd_inc = 0
    rd_limb = 0

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        self.rs = self.rs1
        if self.MNEM.get(self.fun) == 'ldr':
            self.rs_dmem, self.rs_inc, self.rs_limb = self.reg_as_limb(self.rs)
            self.rd_dmem, self.rd_inc, self.rd_limb = self.reg_as_limb(self.rd)
            if self.rs_dmem or self.rd_dmem:
                self.malformed = True  # No dmem access in ldr instruction

    def get_asm_str(self):
        asm_str = ''
        if self.MNEM.get(self.fun) == 'mov':
            asm_str += self.MNEM.get(self.fun) + ' r' + str(self.rd) + ', r' + str(self.rs)
        else:
            asm_str += self.MNEM.get(self.fun) + ' *' + str(self.rd_limb)
            if self.rd_inc:
                asm_str += '++'
            asm_str += ', *' + str(self.rs_limb)
            if self.rs_inc:
                asm_str += '++'
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        if self.MNEM.get(self.fun) == 'mov':
            enc_tab += '|< op ><f|><rd >< |0 ><rs1>|<   0  >|'
        else:
            enc_tab += '|< op ><f|>0?<l>< |0 >0?<r>|<   0  >|\n'
            enc_tab += '            |- inc l   |- inc r'
        return enc_tab

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        ret = 0
        if mnem == 'mov':
            left_reg, right_reg = _get_double_reg(params)
            if left_reg < 0 or left_reg >= 2**cls.REG_LEN:
                raise OverflowError('left reg index out of bounds')
            if right_reg < 0 or right_reg >= 2**cls.REG_LEN:
                raise OverflowError('right reg index out of bounds')
            ret += cls.enc_rd(left_reg)
            ret += cls.enc_rs1(right_reg)
        elif mnem == 'ldr':
            left_reg, linc, right_reg, rinc = _get_double_limb(params)
            if left_reg < 0 or left_reg >= 2**cls.LIMB_LEN:
                raise OverflowError('left limb index out of bounds')
            if right_reg < 0 or right_reg >= 2**cls.LIMB_LEN:
                raise OverflowError('right limb index out of bounds')
            ret += cls.enc_rd(cls.enc_limb_for_reg(left_reg, linc, 0))
            ret += cls.enc_rs1(cls.enc_limb_for_reg(right_reg, rinc, 0))
        else:
            raise Exception('Internal error: Unexpected mnemonic')
        ret += cls.enc_op(cls.OP)
        ret += cls.enc_fun(cls.get_bin_for_mnem(mnem))
        return cls(ret, ctx.ins_ctx)

    def convert_otbn(self, addr):
        if self.MNEM.get(self.fun) == 'mov':
            return [IBnMov(self.rd, self.rs, self.ctx)]
        if self.MNEM.get(self.fun) == 'ldr':
            xd = self.rd_limb + 8  # rfp currently mapped on x8 to x15
            xs = self.rs_limb + 8  # rfp currently mapped on x8 to x15
            logging.info("OTBN conversion: Mapping rfp limb " + str(self.rd_limb) + " on GPR x" + str(xd))
            logging.info("OTBN conversion: Mapping rfp limb " + str(self.rs_limb) + " on GPR x" + str(xs))
            return [IBnMovr(xd, self.rd_inc, xs, self.rs_inc, self.ctx)]
        return None

    def execute(self, m):
        if self.MNEM.get(self.fun) == 'mov':
            m.set_reg(self.rd, m.get_reg(self.rs))
        elif self.MNEM.get(self.fun) == 'ldr':
            sptr = m.get_reg_limb('rfp', self.rs_limb) & m.reg_idx_mask
            dptr = m.get_reg_limb('rfp', self.rd_limb) & m.reg_idx_mask
            m.set_reg(dptr, m.get_reg(sptr))
            if self.rs_inc:
                sptr += 1 % m.NUM_REGS
                m.set_reg_limb('rfp', self.rs_limb, sptr)
            if self.rd_inc:
                dptr += 1 % m.NUM_REGS
                m.set_reg_limb('rfp', self.rd_limb, dptr)

            m.stat_record_wide_mem_op('ldr', self.rs_inc, self.rd_inc)
        else:
            raise Exception('InvalidOpcode')
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IMovi(GIWideImm):
    """Move immediate"""
    S_POS_IN_FUNI = 0
    S_LEN_IN_FUNI = 1

    MNEM = 'movi'
    OP = 0b100000

    zero_ranges = []

    slice = 0

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        self.slice = self.get_gen_bit_slice(self.funi, self.S_POS_IN_FUNI, self.S_LEN_IN_FUNI)

    def get_asm_str(self):
        limb = self.fun
        asm_str = self.MNEM + ' r' + str(self.rd) + '.' + str(limb)
        if self.slice:
            asm_str += 'h'
        else:
            asm_str += 'l'
        asm_str += ', #' + str(self.imm)
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        enc_tab += '|< op ><l|><rd >0S|<       |imm    >|\n'
        enc_tab += 'l: limb; S=1: upper 16 bit; S=0: lower 16 bit'
        return enc_tab

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        ret = 0
        reg, limb, s, imm = _get_reg_limb_and_imm(params)
        ret += cls.enc_imm(imm)
        ret += cls.enc_funi(s)
        ret += cls.enc_rd(reg)
        ret += cls.enc_fun(limb)
        ret += cls.enc_op(cls.OP)
        return cls(ret, ctx.ins_ctx)

    def convert_otbn(self, addr, next_ins=None):
        return None
        lower_12b = 0
        upper_20b = 0
        addi_ins = IOtAddi(self.rd, 0, lower_12b, self.ctx)
        lui_ins = IOtLui(self.rd, upper_20b, self.ctx)
        return [addi_ins, lui_ins]

    def execute(self, m):
        m.stat_record_movi(self.imm.bit_length())
        m.set_reg_half_limb(self.rd, self.fun, self.imm, self.slice)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class ISt(GIStd):
    """Indexed Store"""
    MNEM = {0: 'st'}
    OP = 0b100100

    zero_ranges = [GIStd.RS2_RANGE, GIStd.IMM_RANGE]

    dmem_dst = 0
    inc_dst = 0
    limb_dst = 0
    dmem_src = 0
    inc_src = 0
    limb_src = 0

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        self.dmem_dst, self.inc_dst, self.limb_dst = self.reg_as_limb(self.rd)
        self.dmem_src, self.inc_src, self.limb_src = self.reg_as_limb(self.rs1)
        if not self.dmem_dst:
            self.malformed = True  # destination always in dmem with st instruction
        if self.dmem_src:
            self.malformed = True  # source never in dmem with st instruction

    def get_asm_str(self):
        asm_str = ''
        asm_str += self.MNEM.get(self.fun) + ' *' + str(self.limb_src)
        if self.inc_src:
            asm_str += '++'
        asm_str += ', *' + str(self.limb_dst)
        if self.inc_dst:
            asm_str += '++'
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        enc_tab += '|< op ><f|>1i<d>< |0 >0i<s>|<   0  >|'
        return enc_tab

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        ret = 0
        left_limb, left_inc, right_limb, right_inc = _get_double_limb(params)
        if left_limb < 0 or left_limb >= 2**cls.LIMB_LEN:
            raise OverflowError('Left limb index out of bounds')
        if right_limb < 0 or right_limb >= 2**cls.LIMB_LEN:
            raise OverflowError('Right limb index out of bounds')
        ret += cls.enc_rd(cls.enc_limb_for_reg(right_limb, right_inc, 1))
        ret += cls.enc_rs1(cls.enc_limb_for_reg(left_limb, left_inc, 0))
        ret += cls.enc_fun(cls.get_bin_for_mnem(mnem))
        ret += cls.enc_op(cls.OP)
        return cls(ret, ctx.ins_ctx)

    def convert_otbn(self, addr):
        xd = self.limb_dst + 16  # dmp currently mapped on x16 to x23
        xs = self.limb_src + 8   # rfp currently mapped on x8 to x15
        offset = 0
        logging.info("OTBN conversion: Mapping dmp limb " + str(self.limb_src) + " on GPR x" + str(xd))
        logging.info("OTBN conversion: Mapping rfp limb " + str(self.limb_dst) + " on GPR x" + str(xs))
        if self.inc_src and self.inc_dst:
            return [IBnSid(xs, 0, xd, 1, offset, self.ctx), IOtAddi(xs, xs, 1, self.ctx)]
        else:
            return [IBnSid(xs, self.inc_src, xd, self.inc_dst, offset, self.ctx)]

    def execute(self, m):
        sptr = m.get_reg_limb('rfp', self.limb_src) & m.reg_idx_mask
        dptr = m.get_reg_limb('dmp', self.limb_dst) & m.dmem_idx_mask
        m.set_dmem(dptr, m.get_reg(sptr))
        if self.inc_src:
            sptr += 1 % m.NUM_REGS
            m.set_reg_limb('rfp', self.limb_src, sptr)
        if self.inc_dst:
            dptr += 1 % m.DMEM_DEPTH
            m.set_reg_limb('dmp', self.limb_dst, dptr)
        trace_str = self.get_asm_str()[1]

        m.stat_record_wide_mem_op('st', self.inc_src, self.inc_dst)

        return trace_str, None


class ILd(GIStd):
    """Indexed Load"""
    MNEM = {0: 'ldc', 1: 'ld'}  # encoded via dmem bit of limb in rs
    OP = 0b100011

    zero_ranges = [GIStd.RS2_RANGE, GIStd.IMM_RANGE]

    dmem_dst = 0
    inc_dst = 0
    limb_dst = 0
    dmem_src = 0
    inc_src = 0
    limb_src = 0

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        self.dmem_dst, self.inc_dst, self.limb_dst = self.reg_as_limb(self.rd)
        self.dmem_src, self.inc_src, self.limb_src = self.reg_as_limb(self.rs1)
        if self.dmem_src == self.dmem_dst:
            self.malformed = True

    def get_asm_str(self):
        asm_str = ''
        asm_str += self.MNEM.get(self.dmem_src) + ' *' + str(self.limb_dst)
        if self.inc_dst:
            asm_str += '++'
        asm_str += ', *' + str(self.limb_src)
        if self.inc_src:
            asm_str += '++'
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        if self.dmem_src:
            enc_tab += '|< op ><f|>0i<d>< |0 >1i<s>|<   0  >|'
        else:
            enc_tab += '|< op ><f|>1i<d>< |0 >0i<s>|<   0  >|'
        return enc_tab

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        ret = 0
        left_limb, left_inc, right_limb, right_inc = _get_double_limb(params)
        if left_limb < 0 or left_limb >= 2**cls.LIMB_LEN:
            raise OverflowError('left limb index out of bounds')
        if right_limb < 0 or right_limb >= 2**cls.LIMB_LEN:
            raise OverflowError('right limb index out of bounds')
        if mnem == 'ldc':
            ret += cls.enc_rs1(cls.enc_limb_for_reg(right_limb, right_inc, 0))
            ret += cls.enc_rd(cls.enc_limb_for_reg(left_limb, left_inc, 1))
        elif mnem == 'ld':
            ret += cls.enc_rs1(cls.enc_limb_for_reg(right_limb, right_inc, 1))
            ret += cls.enc_rd(cls.enc_limb_for_reg(left_limb, left_inc, 0))
        else:
            raise Exception('Internal error: Invalid mnemonic')
        ret += cls.enc_op(cls.OP)
        return cls(ret, ctx.ins_ctx)

    def convert_otbn(self, addr):
        if self.MNEM.get(self.dmem_src) == 'ld':
            xd = self.limb_dst + 8   # dmp currently mapped on x8 to x15
            xs = self.limb_src + 16  # dmp currently mapped on x16 to x23
            offset = 0
            logging.info("OTBN conversion: Mapping rfp limb " + str(self.limb_dst) + " on GPR x" + str(xd))
            logging.info("OTBN conversion: Mapping dmp limb " + str(self.limb_src) + " on GPR x" + str(xs))
            if self.inc_src and self.inc_dst:
                return [IBnLid(xd, 0, xd, 1, offset, self.ctx), IOtAddi(xd, xd, 1, self.ctx)]
            else:
                return [IBnLid(xd, self.inc_dst, xs, self.inc_src, offset, self.ctx)]
        return None

    def execute(self, m):
        sptr = m.get_reg_limb('dmp', self.limb_src) & m.dmem_idx_mask
        dptr = m.get_reg_limb('rfp', self.limb_dst) & m.reg_idx_mask
        m.set_reg(dptr, m.get_dmem(sptr))
        if self.inc_src:
            sptr += 1 % m.DMEM_DEPTH
            m.set_reg_limb('dmp', self.limb_src, sptr)
        if self.inc_dst:
            dptr += 1 % m.NUM_REGS
            m.set_reg_limb('rfp', self.limb_dst, dptr)
        trace_str = self.get_asm_str()[1]

        # XXX: assert on ldc
        m.stat_record_wide_mem_op('ld', self.inc_src, self.inc_dst)

        return trace_str, None


#############################################
#                 Other                     #
#############################################

class INop(GIStdNoParm):
    """No operation"""
    MNEM = {0: 'nop'}
    OP = 0b111111

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def convert_otbn(self, addr):
        logging.info("Converting nop to ADDI x0, x0, 0 ")
        return [IOtAddi(0, 0, 0, self.ctx)]
        #return [IOtAddi(0, 0, 0, self.ctx), IOtAddi(0, 0, 0, self.ctx), IOtAddi(0, 0, 0, self.ctx)]

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        if params:
            raise SyntaxError('Unexpected parameters with nop instruction')
        ret = cls.enc_op(cls.OP)
        return cls(ret, ctx.ins_ctx)

    def execute(self, m):
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class ISigini(GIStd):
    """Tag"""
    MNEM = {0: 'sigini'}
    OP = 0b111110

    zero_ranges = [Ins.FUN_RANGE, GIStd.RD_RANGE, GIStd.RS2_RANGE, GIStd.RS1_RANGE]

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def get_asm_str(self):
        asm_str = self.MNEM.get(self.fun) + ' #' + str(self.imm)
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        enc_tab += '|< op >< |     0  |        |<  tag >|'
        return enc_tab

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        ret = 0
        ret += cls.enc_imm(_get_imm(params))
        ret += cls.enc_op(cls.OP)
        return cls(ret, ctx.ins_ctx)

    def execute(self, m):
        trace_str = self.get_asm_str()[1]
        return trace_str, None


#############################################
#              Flow Control                 #
#############################################

class IRet(GIStdNoParm):
    """Return from subroutine"""
    MNEM = {0: 'ret'}
    OP = 0b000011

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        if params:
            raise SyntaxError('Unexpected parameters with ret instruction')
        ret = cls.enc_op(cls.OP)
        return cls(ret, ctx.ins_ctx)

    def convert_otbn(self, addr):
        return [IOtJalr(0, 1, 0, self.ctx)]

    def execute(self, m):
        try:
            ret_addr = m.pop_call_stack()
        except CallStackUnderrun:
            if m.get_pc() == m.stop_addr:
                # We have an underrun but are at the stop address anyways, so this is fine
                ret_addr = m.get_pc()
            else:
                m.finish()
                ret_addr = m.get_pc()

        trace_str = self.get_asm_str()[1]
        return trace_str, ret_addr


class ICall(GIMidImm):
    MNEM = {0: 'call'}
    OP = 0b000010

    ZERO_RANGES = [Ins.FUN_RANGE, GIMidImm.FUNB_RANGE]

    def __init__(self, ret, ctx, label=False):
        self.label = label
        super().__init__(ret, ctx)

    def get_asm_str(self):
        addr = self.imm
        asm_str = self.MNEM.get(self.fun) + ' &' + self.ctx.get_or_add_function(addr)
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        enc_tab += '|< op ><0|><     0|   ><   |addr   >|'
        return enc_tab

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        func_label = params[1:].strip()
        dest_addr = ctx.get_addr_for_function_name(params)
        ret = 0
        ret += cls.enc_imm(dest_addr)
        ret += cls.enc_op(cls.OP)
        return cls(ret, ctx.ins_ctx, func_label)

    def convert_otbn(self, addr):
        jal_imm = self.imm - addr
        return [IOtJal(1, jal_imm, addr, self.ctx, label=self.label)]

    def execute(self, m):
        m.stat_record_func_call(call_site = m.pc, callee_func = self.imm)

        m.push_call_stack(m.get_pc()+1)

        trace_str = self.get_asm_str()[1]
        return trace_str, self.imm


class IBranch(GIMidImm):

    MNEM = {0b00000000001: 'bl',
            0b00010001000: 'bnc',
            0b00010000000: 'b',
            0b00010000100: 'bnz',
            0b00000000100: 'bz'}
    OP = 0b000100

    zero_ranges = [Ins.FUN_RANGE]

    def __init__(self, ins, ctx, label=None):
        self.label = label
        super().__init__(ins, ctx)

    def get_asm_str(self):
        addr = self.imm
        asm_str = self.MNEM.get(self.funb) + ' ' + self.ctx.get_or_add_label(addr)
        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        enc_tab += '|< op ><0|><  funb|   ><   |addr   >|'
        return enc_tab

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        label = params
        dest_addr = ctx.get_addr_for_label(params)
        ret = 0
        ret += cls.enc_imm(dest_addr)
        funb = cls.get_bin_for_mnem(mnem)
        ret += cls.enc_funb(funb)
        ret += cls.enc_op(cls.OP)
        return cls(ret, ctx.ins_ctx, label)

    def convert_otbn(self, addr):
        offset = self.imm - addr
        if self.MNEM.get(self.funb) == 'bc':
            ins_read_csr = IOtCsrrs(2, Machine.CSR_FLAG, 0, self.ctx)
            ins_andi = IOtAndi(2, 2, 1, self.ctx)
            ins_branch = IOtBne(2, 0, offset, addr, self.ctx, self.label)
            return [ins_read_csr, ins_andi, ins_branch]
        if self.MNEM.get(self.funb) == 'bl':
            ins_read_csr = IOtCsrrs(2, Machine.CSR_FLAG, 0, self.ctx)
            ins_andi = IOtAndi(2, 2, 2, self.ctx)
            ins_branch = IOtBne(2, 0, offset, addr, self.ctx, self.label)
            return [ins_read_csr, ins_andi, ins_branch]
        if self.MNEM.get(self.funb) == 'bm':
            ins_read_csr = IOtCsrrs(2, Machine.CSR_FLAG, 0, self.ctx)
            ins_andi = IOtAndi(2, 2, 4, self.ctx)
            ins_branch = IOtBne(2, 0, offset, addr, self.ctx, self.label)
            return [ins_read_csr, ins_andi, ins_branch]
        if self.MNEM.get(self.funb) == 'bz':
            ins_read_csr = IOtCsrrs(2, Machine.CSR_FLAG, 0, self.ctx)
            ins_andi = IOtAndi(2, 2, 8, self.ctx)
            ins_branch = IOtBne(2, 0, offset, addr, self.ctx, self.label)
            return [ins_read_csr, ins_andi, ins_branch]
        if self.MNEM.get(self.funb) == 'bnc':
            ins_read_csr = IOtCsrrs(2, Machine.CSR_FLAG, 0, self.ctx)
            ins_andi = IOtAndi(2, 2, 1, self.ctx)
            ins_branch = IOtBeq(2, 0, offset, addr, self.ctx, self.label)
            return [ins_read_csr, ins_andi, ins_branch]
        if self.MNEM.get(self.funb) == 'bnl':
            ins_read_csr = IOtCsrrs(2, Machine.CSR_FLAG, 0, self.ctx)
            ins_andi = IOtAndi(2, 2, 2, self.ctx)
            ins_branch = IOtBeq(2, 0, offset, addr, self.ctx, self.label)
            return [ins_read_csr, ins_andi, ins_branch]
        if self.MNEM.get(self.funb) == 'bnm':
            ins_read_csr = IOtCsrrs(2, Machine.CSR_FLAG, 0, self.ctx)
            ins_andi = IOtAndi(2, 2, 4, self.ctx)
            ins_branch = IOtBeq(2, 0, offset, addr, self.ctx, self.label)
            return [ins_read_csr, ins_andi, ins_branch]
        if self.MNEM.get(self.funb) == 'bnz':
            ins_read_csr = IOtCsrrs(2, Machine.CSR_FLAG, 0, self.ctx)
            ins_andi = IOtAndi(2, 2, 8, self.ctx)
            ins_branch = IOtBeq(2, 0, offset, addr, self.ctx, self.label)
            return [ins_read_csr, ins_andi, ins_branch]
        if self.MNEM.get(self.funb) == 'b':
            return [IOtJal(0, offset, addr, self.ctx, self.label)]
        logging.warning('Unknown opcode at address ' + self.addr + '. Cannot convert instruction.')
        return None

    def execute(self, m):
        trace_str = self.get_asm_str()[1]
        if self.MNEM.get(self.funb) == 'bl':
            branch = m.get_flag('L')
        elif self.MNEM.get(self.funb) == 'bnc':
            branch = not m.get_flag('C')
        elif self.MNEM.get(self.funb) == 'b':
            branch = True
        elif self.MNEM.get(self.funb) == 'bnz':
            branch = not m.get_flag('Z')
        elif self.MNEM.get(self.funb) == 'bz':
            branch = m.get_flag('Z')
        else:
            raise Exception('Invalid opcode')
        if branch:
            return trace_str, self.imm
        return trace_str, None


class ILoop(GIMidImm):
    """Loop instruction"""
    MNEM = 'loop'
    OP = 0b000001

    RS_POS_IN_FUNB = 1
    FUN_DIRECT = 2
    FUN_INDIRECT = 4

    CNT_LEN = 11
    CNT_POS = 0
    LEN_POS = 0

    zero_ranges = [(23, 23)]

    len = 0
    cnt = 0
    limb = 0

    def __init__(self, ins, ctx):
        super().__init__(ins, ctx)

    def dec(self):
        super().dec()
        self.len = self.imm
        if self.fun == self.FUN_DIRECT:  # pound/direct case
            self.cnt = self.funb
        elif self.fun == self.FUN_INDIRECT:  # star/indirect case
            rs = self.get_gen_bit_slice(self.funb, self.RS_POS_IN_FUNB, self.REG_LEN)
            dmem, inc, self.limb = self.reg_as_limb(rs)
            if dmem:
                self.malformed = True
            if inc:
                self.malformed = True
        else:
            raise InvalidOp2

    def get_asm_str(self):
        asm_str = self.MNEM
        if self.fun == self.FUN_DIRECT:  # pound/direct case
            asm_str += ' #' + str(self.cnt) + ' ('
        elif self.fun == 4:  # star/indirect case
            asm_str += ' *' + str(self.limb) + ' ('
        else:
            raise InvalidOp2

        return self.get_hexstr(), asm_str, self.malformed

    def get_enc_tab(self):
        enc_tab = self.get_enc_table_hdr() + '\n'
        enc_tab += self.get_bin_with_separators() + '\n'
        if self.fun == self.FUN_DIRECT:  # pound case
            enc_tab += '|< op ><o2><  count   ><      len  >|'
        elif self.fun == self.FUN_INDIRECT:  # star case
            enc_tab += '|< op ><o2><   0   ><l>0<      len  >|'
        else:
            raise InvalidOp2
        return enc_tab

    def get_len(self):
        return self.len

    @classmethod
    def enc_loop_imm_cnt(cls, imm):
        if imm < 0 or imm >= 2**cls.CNT_LEN:
            raise OverflowError('Loop immediate out of bounds')
        return imm << cls.CNT_POS

    @classmethod
    def enc_lc_len(cls, limb):
        if limb < 0 or limb >= 2**cls.LIMB_LEN:
            raise OverflowError('limb reference out of bounds')
        return limb << cls.RS_POS_IN_FUNB

    @classmethod
    def enc_loop_len(cls, llen):
        if llen < 0 or llen >= 2**cls.IMM_LEN:
            raise OverflowError('immediate out of bounds')
        return llen << cls.LEN_POS

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        cl_addr = ctx.get_loop_close_addr(addr)
        length = cl_addr - addr - 1
        if length < 0:
            raise Exception('Internal error: inconsistent loop length table')
        ret = 0
        if _get_loop_type_direct(params):
            cnt = _get_imm_with_paren(params)
            ret += cls.enc_funb(cls.enc_loop_imm_cnt(cnt))
            ret += cls.enc_fun(cls.FUN_DIRECT)
        else:
            limb = _get_limb_with_paren(params)
            ret += cls.enc_funb(cls.enc_lc_len(limb))
            ret += cls.enc_fun(cls.FUN_INDIRECT)
        ret += cls.enc_loop_len(length)
        ret += cls.enc_op(cls.OP)
        return cls(ret, ctx.ins_ctx)

    def convert_otbn(self, addr):
        if self.fun == self.FUN_INDIRECT:  # star/indirect case
            gpr = self.limb + 24  # lc currently mapped on x24 to x31
            logging.info("OTBN conversion: Mapping lc limb " + str(self.limb) + " on GPR x" + str(gpr))
            return [IOtLoop(gpr, self.len, self.ctx)]
        else:
            return [IOtLoopi(self.cnt, self.len, self.ctx)]

    def execute(self, m):
        if self.fun == self.FUN_INDIRECT:  # star/indirect case
            self.cnt = m.get_reg_limb('lc', self.limb)
        m.push_loop_stack(self.cnt-1, self.len+m.get_pc(), m.get_pc()+1)
        m.stat_record_loop(m.get_pc(), self.len, len(m.loop_stack), self.cnt)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


if __name__ == "__main__":
    raise Exception('This file is not executable')
