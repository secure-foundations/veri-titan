# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from . machine import *

I_TYPE_IMM_WIDTH = Machine.I_TYPE_IMM_WIDTH
NUM_GPRS = Machine.NUM_GPRS
NUM_WRDS = Machine.NUM_REGS


#############################################
#                 Parsers                   #
#############################################

def _get_imm(asm_str):
    """return int for immediate string and check proper formatting"""
    if len(asm_str.strip().split()) > 1:
        raise SyntaxError('Unexpected separator in immediate')
    if not asm_str.strip().isdigit():
        raise SyntaxError('Immediate not a number')
    return int(asm_str.strip())


def _get_single_wdr_with_hw_sel(asm_str):
    """returns a single register from string with half word select and check proper formatting (e.g "w5.u")"""
    if len(asm_str.split()) > 1:
        raise SyntaxError('Unexpected separator in reg reference')
    if not asm_str.lower().startswith('w'):
        raise SyntaxError('Missing \'w\' character at start of reg reference')
    if not (asm_str.lower().endswith('.u') or asm_str.lower().endswith('.l')):
        raise SyntaxError('Missing \'.L\' or \'.U\' at end of reg reference')
    if not asm_str[1:-2].isdigit():
        raise SyntaxError('reg reference not a number')
    if asm_str[-2:].lower() == '.u':
        hw_sel = 'upper'
    if asm_str[-2:].lower() == '.l':
        hw_sel = 'lower'
    return int(asm_str[1:-2]), hw_sel


def _get_single_wdr_with_qw_sel(asm_str):
    """returns a single register from string with quad word select and check proper formatting (e.g "w5.2")"""
    if len(asm_str.split()) > 1:
        raise SyntaxError('Unexpected separator in reg reference')
    if not asm_str.lower().startswith('w'):
        raise SyntaxError('Missing \'w\' character at start of reg reference')
    if not (asm_str.lower().endswith('.0') or asm_str.lower().endswith('.1') or asm_str.lower().endswith('.2')
            or asm_str.lower().endswith('.3')):
        raise SyntaxError('Missing quad word selection (\'.0\', \'.1\', \'.2\' or \'.3\') at end of reg reference')
    if not asm_str[1:-2].isdigit():
        raise SyntaxError('reg reference not a number')
    qw_sel = int(asm_str[-1])
    return int(asm_str[1:-2]), qw_sel


def _get_single_shifted_wdr(asm_str):
    """decode a reg in (possible) shift notation (e.g. "w4 >> 128")"""
    if '>>' in asm_str:
        shift_type = 'right'
        substr = asm_str.split('>>')
    elif '<<' in asm_str:
        shift_type = 'left'
        substr = asm_str.split('<<')
    else:
        return _get_single_wdr(asm_str), False, 0

    if len(substr) != 2:
        raise SyntaxError('Syntax error in parameter set in input shift notation. '
                          'Expected reg and shift immediate')

    wdr = _get_single_wdr(substr[0].strip())
    if substr[1].strip().lower().endswith('b'):
        if not substr[1].strip()[:-1].isdigit():
            raise SyntaxError('input shift immediate not a number')
        shift_bytes = int(substr[1].strip()[:-1])
        shift_bits = int(shift_bytes)*8
    else:
        shift_bits_str = substr[1].strip()
        if not shift_bits_str.isdigit():
            raise SyntaxError('input shift immediate not a number')
        shift_bits = int(shift_bits_str)

    return wdr, shift_type, shift_bits


def _get_optional_flag_group_and_flag(asm_str):
    """decode a flag with optional flag group (e.g FG1.L or just M)"""
    substr = asm_str.split('.')
    if len(substr) > 2:
        raise SyntaxError('Malformed flag group and/or flag reference')
    if len(substr) == 2:
        if substr[0] == 'fg0':
            flag_group = 'standard'
        if substr[0] == 'fg1':
            flag_group = 'extension'
        else:
            raise SyntaxError('Flag group must be either FG0 for standard or FG1 for extension')
        flag = substr[1].lower()
    else:
        flag = asm_str.lower()
        flag_group = 'standard'
    if not (flag == 'c' or flag == 'm' or flag == 'l' or flag == 'z'):
        raise SyntaxError('Illegal flag reference')
    return flag_group, flag


def _get_flag_group(asm_str):
    substr = asm_str.strip().lower()
    if substr == 'fg0':
        return 'default'
    elif substr == 'fg1':
        return 'extension'
    else:
        raise SyntaxError('Syntax error: invalid flag group')


def _get_three_wdr_with_flag_group_and_shift(asm_str):
    """decode the full BN standard format with wd, ws1 and optional flag group and
    possibly shifted rs2 (e.g.: "w21, w5, w7 >> 128")"""
    substr = asm_str.split(',')
    if not (len(substr) == 3 or len(substr) == 4):
        raise SyntaxError('Syntax error in parameter set. Expected three reg references and optional flag group')
    wrd = _get_single_wdr(substr[0].strip())
    wrs1 = _get_single_wdr(substr[1].strip())
    wrs2, shift_type, shift_bits = _get_single_shifted_wdr(substr[2].strip())
    flag_group = 'standard'
    if len(substr) == 4:
        flag_group = _get_flag_group(substr[3].strip())
    return wrd, wrs1, wrs2, shift_type, shift_bits, flag_group


def _get_two_wdr_with_flag_group_and_shift(asm_str):
    """decode the full BN compare format with ws1 and optional flag group and
    possibly shifted rs2 (e.g.: "w5, w7 >> 128")"""
    substr = asm_str.split(',')
    if not (len(substr) == 2 or len(substr) == 3):
        raise SyntaxError('Syntax error in parameter set. Expected two reg references and optional flag group')
    wrs1 = _get_single_wdr(substr[0].strip())
    wrs2, shift_type, shift_bits = _get_single_shifted_wdr(substr[1].strip())
    flag_group = 'standard'
    if len(substr) == 3:
        flag_group = _get_flag_group(substr[2].strip())
    return wrs1, wrs2, shift_type, shift_bits, flag_group


def _get_three_wdr_with_flag_group_and_flag(asm_str):
    """decode the full BN format with wrd, wrs1, optional flag group and flag"""
    substr = asm_str.split(',')
    if not (len(substr) == 4):
        raise SyntaxError('Syntax error in parameter set. Expected three reg references and flag')
    wrd = _get_single_wdr(substr[0].strip())
    wrs1 = _get_single_wdr(substr[1].strip())
    wrs2 = _get_single_wdr(substr[2].strip())
    flag_group, flag = _get_optional_flag_group_and_flag(substr[3].lower().strip())
    return wrd, wrs1, wrs2, flag_group, flag


def _get_two_wdr_with_shift(asm_str):
    """decode the BN format with wrd, wrs and possibly shifted wrs (e.g.: "w21, w7 >> 128")"""
    substr = asm_str.split(',')
    if not (len(substr) == 2):
        raise SyntaxError('Syntax error in parameter set. Expected two reg references')
    wrd = _get_single_wdr(substr[0].strip())
    wrs, shift_type, shift_bits = _get_single_shifted_wdr(substr[1].strip())
    return wrd, wrs, shift_type, shift_bits


def _get_three_wdr_with_two_half_word_sels(asm_str):
    """decode the BN format for half word mul with wrd, wrs1 and wrs2 and half word selectors for the source regs"""
    substr = asm_str.split(',')
    if not len(substr) == 3:
        raise SyntaxError('Syntax error in parameter set. Expected three reg references')
    wrd = _get_single_wdr(substr[0].strip())
    wrs1, wrs1_hw_sel = _get_single_wdr_with_hw_sel(substr[1].strip())
    wrs2, wrs2_hw_sel = _get_single_wdr_with_hw_sel(substr[2].strip())
    return wrd, wrs1, wrs1_hw_sel, wrs2, wrs2_hw_sel


def _get_wdr_with_halfw_sel_two_wdr_with_quadw_sel_and_imm(asm_str):
    """decode the BN format for half word sel for first wdr, quater word sel for 2nd and 3rd wdr and imm"""
    substr = asm_str.split(',')
    if not len(substr) == 4:
        raise SyntaxError('Syntax error in parameter set. Expected four reg references')
    wrd, wrd_hw_sel = _get_single_wdr_with_hw_sel(substr[0].strip())
    wrs1, wrs1_qw_sel = _get_single_wdr_with_qw_sel(substr[1].strip())
    wrs2, wrs2_qw_sel = _get_single_wdr_with_qw_sel(substr[2].strip())
    imm = _get_imm(substr[3].strip())
    return wrd, wrd_hw_sel, wrs1, wrs1_qw_sel, wrs2, wrs2_qw_sel, imm


def _get_two_wdr_with_quadw_sel_and_imm(asm_str):
    """decode the BN format for quarter word sel for two wdrs and imm"""
    substr = asm_str.split(',')
    if not len(substr) == 3:
        raise SyntaxError('Syntax error in parameter set. Expected three reg references')
    wrs1, wrs1_qw_sel = _get_single_wdr_with_qw_sel(substr[0].strip())
    wrs2, wrs2_qw_sel = _get_single_wdr_with_qw_sel(substr[1].strip())
    imm = _get_imm(substr[2].strip())
    return wrs1, wrs1_qw_sel, wrs2, wrs2_qw_sel, imm


def _get_two_wdr(asm_str):
    """decode the BN format with wrd and wrs"""
    substr = asm_str.split(',')
    if not (len(substr) == 2):
        raise SyntaxError('Syntax error in parameter set. Expected three reg references')
    wrd = _get_single_wdr(substr[0].strip())
    wrs = _get_single_wdr(substr[1].strip())
    return wrd, wrs


def _get_three_wdr(asm_str):
    """decode the BN format with wrd, wrs1 and wrs2 (e.g.: "w21, w5, w7")"""
    substr = asm_str.split(',')
    if not (len(substr) == 3):
        raise SyntaxError('Syntax error in parameter set. Expected three reg references')
    wrd = _get_single_wdr(substr[0].strip())
    wrs1 = _get_single_wdr(substr[1].strip())
    wrs2 = _get_single_wdr(substr[2].strip())
    return wrd, wrs1, wrs2


def _get_two_wdr_and_imm_with_flag_group(asm_str):
    """decode the BN immediate standard format with wrd, wrs and optional flag group"""
    substr = asm_str.split(',')
    if not (len(substr) == 3 or len(substr) == 4):
        raise SyntaxError('Syntax error in parameter set. Expected two reg references + '
                          'immediate and optional flag group')
    wrd = _get_single_wdr(substr[0].strip())
    wrs = _get_single_wdr(substr[1].strip())
    imm = _get_imm(substr[2].strip())
    flag_group = 'standard'
    if len(substr) == 4:
        flag_group = _get_flag_group(substr[3].strip())
    return wrd, wrs, imm, flag_group


def _get_two_imm(asm_str):
    """decode the BN format with two immediates"""
    substr = asm_str.split(',')
    if not (len(substr) == 2):
        raise SyntaxError('Syntax error in parameter set. Expected two immediates')
    imm1 = _get_imm(substr[0].strip())
    imm2 = _get_imm(substr[1].strip())
    return imm1, imm2


def _get_gpr_and_imm(asm_str):
    """decode the BN format with gpr and immediate"""
    substr = asm_str.split(',')
    if not (len(substr) == 2):
        raise SyntaxError('Syntax error in parameter set. Expected GPR and immediate')
    gpr = _get_single_gpr(substr[0].strip().lower())
    imm = _get_imm(substr[1])
    return gpr, imm


def _get_gpr_and_optional_imm(asm_str):
    """decode the BN format with gpr and optional immediate"""
    substr = asm_str.split(',')
    if not (len(substr) == 1 or len(substr) == 2):
        raise SyntaxError('Syntax error in parameter set. Expected GPR and optional immediate')
    gpr = _get_single_gpr(substr[0].strip().lower())
    if len(substr) == 2:
        imm = _get_imm(substr[1])
    else:
        imm = None
    return gpr, imm


def _get_gpr_and_label(asm_str):
    """decode the BN format with gpr and label"""
    substr = asm_str.split(',')
    if not (len(substr) == 2):
        raise SyntaxError('Syntax error in parameter set. Expected GPR and label')
    gpr = _get_single_gpr(substr[0].strip().lower())
    label = _get_label(substr[1].strip())
    return gpr, label


def _get_two_gprs_and_label(asm_str):
    """decode the RV format with two GPRRs and label"""
    substr = asm_str.split(',')
    if not (len(substr) == 3):
        raise SyntaxError('Syntax error in parameter set. Expected two GPRs and label')
    gpr1 = _get_single_gpr(substr[0].strip().lower())
    gpr2 = _get_single_gpr(substr[1].strip().lower())
    label = _get_label(substr[2].strip())
    return gpr1, gpr2, label


def _get_gpr_imm_gpr(asm_str):
    """decode the RV format with gpr followed by immediate followed by GPR"""
    substr = asm_str.split(',')
    if not (len(substr) == 3):
        raise SyntaxError('Syntax error in parameter set. Expected two GPRs and immediate')
    gpr1 = _get_single_gpr(substr[0].strip().lower())
    imm = _get_imm(substr[1].strip())
    gpr2 = _get_single_gpr(substr[2].strip().lower())
    return gpr1, imm, gpr2


def _get_wdr_imm_wd(asm_str):
    """decode the BN format with wdr followed by immediate followed by wdr"""
    substr = asm_str.split(',')
    if not (len(substr) == 3):
        raise SyntaxError('Syntax error in parameter set. Expected two GPRs and immediate')
    wrd1 = _get_single_wdr(substr[0].strip().lower())
    imm = _get_imm(substr[1].strip())
    wrd2 = _get_single_wdr(substr[2].strip().lower())
    return wrd1, imm, wrd2


def _get_two_gprs_with_inc(asm_str):
    """decode standard format with two possibly incremented GPRs (e.g.: "x20, x21++")"""
    substr = asm_str.split(',')
    if len(substr) != 2:
        raise SyntaxError('Syntax error in parameter set. Expected two GPR references')
    xd, inc_xd = _get_single_inc_gpr(substr[0].strip())
    xs, inc_xs = _get_single_inc_gpr(substr[1].strip())
    return xd, inc_xd, xs, inc_xs


def _get_two_gprs_with_imm(asm_str):
    """decode standard format with two GPRs and immediate (e.g.: "x20, x21, 5")"""
    substr = asm_str.split(',')
    if len(substr) != 3:
        raise SyntaxError('Syntax error in parameter set. Expected two GPR references and immediate')
    x1 = _get_single_gpr(substr[0].strip())
    x2 = _get_single_gpr(substr[1].strip())
    if not substr[2].strip().isdigit():
        raise SyntaxError('immediate not a number')
    return x1, x2, int(substr[2].strip())


def _get_three_gprs(asm_str):
    """decode standard format with two GPRs and immediate (e.g.: "x20, x21, 5")"""
    substr = asm_str.split(',')
    if len(substr) != 3:
        raise SyntaxError('Syntax error in parameter set. Expected three GPR references')
    x1 = _get_single_gpr(substr[0].strip())
    x3 = _get_single_gpr(substr[1].strip())
    x2 = _get_single_gpr(substr[2].strip())
    return x1, x2, x3


def _get_two_gprs_with_inc_and_offset(asm_str):
    """decode standard format with two possibly incremented GPRs and offset (e.g.: "x20, 128(x21++)"""
    substr = asm_str.split(',')
    if len(substr) != 2:
        raise SyntaxError('Syntax error in parameter set. Expected two GPR references')
    x1, inc_x1 = _get_single_inc_gpr(substr[0].strip())
    x2, inc_x2, offset = _get_single_inc_gpr_with_offset(substr[1].strip())
    return x1, inc_x1, x2, inc_x2, offset


def _get_two_gprs_with_offset(asm_str):
    """decode standard format with two GPRs and offset (e.g.: "x20, 128(x21)"""
    substr = asm_str.split(',')
    if len(substr) != 2:
        raise SyntaxError('Syntax error in parameter set. Expected two GPR references')
    x1 = _get_single_gpr(substr[0].strip())
    x2, offset = _get_single_gpr_with_offset(substr[1].strip())
    return x1, offset, x2


def _get_single_wdr(asm_str):
    """returns a single register from string and check proper formatting (e.g "w5")"""
    if len(asm_str.split()) > 1:
        raise SyntaxError('Unexpected separator in reg reference')
    if not asm_str.lower().startswith('w'):
        raise SyntaxError('Missing \'w\' character at start of reg reference')
    if not asm_str[1:].isdigit():
        raise SyntaxError('reg reference not a number')
    return int(asm_str[1:])


def _get_single_gpr(asm_str):
    """returns a single GPR from string and check proper formatting (e.g "x5")"""
    if len(asm_str.split()) > 1:
        raise SyntaxError('Unexpected separator in reg reference')
    if not asm_str.lower().startswith('x'):
        raise SyntaxError('Missing \'x\' character at start of reg reference')
    if not asm_str[1:].isdigit():
        raise SyntaxError('reg reference not a number')
    return int(asm_str[1:])


def _get_label(asm_str):
    """returns a single label"""
    if len(asm_str.strip().split()) > 1:
        raise SyntaxError('Unexpected separator in label')
    if len(asm_str.strip()) == 0:
        raise SyntaxError('label expected')
    return asm_str.strip()


def _get_single_inc_gpr(asm_str):
    """returns a single GPR from string and checks inc indicator (e.g "x5" or "x5++")"""
    inc = False
    if len(asm_str.split()) > 1:
        raise SyntaxError('Unexpected separator in reg reference')
    if not asm_str.lower().startswith('x'):
        raise SyntaxError('Missing \'x\' character at start of GPR reference')
    if asm_str.lower().endswith('++'):
        inc = True
        reg = asm_str[1:-2]
    else:
        reg = asm_str[1:]
    if not reg.isdigit():
        raise SyntaxError('GPR reference not a number')
    return int(reg), inc


def _get_single_inc_gpr_with_offset(asm_str):
    """returns a single GPR with offset from string and checks inc indicator (e.g "128(x5)" or "128(x5++)")"""
    inc = False
    if len(asm_str.split()) > 1:
        raise SyntaxError('Unexpected separator in reg reference')
    if not asm_str.lower().endswith(')'):
        raise SyntaxError('Missing \')\'  at end of GPR with offset reference')
    substr = asm_str.split('(')
    if not len(substr) == 2:
        raise SyntaxError('Malformed GPR reference with offset')
    if not substr[0].isdigit():
        raise SyntaxError('Offset reference not a number')
    offset = int(substr[0])
    gpr, inc_gpr = _get_single_inc_gpr(substr[1][:-1].strip().lower())
    return gpr, inc_gpr, offset


def _get_single_gpr_with_offset(asm_str):
    """returns a single GPR with offset from string (e.g "128(x5)")"""
    if len(asm_str.split()) > 1:
        raise SyntaxError('Unexpected separator in reg reference')
    if not asm_str.lower().endswith(')'):
        raise SyntaxError('Missing \')\'  at end of GPR with offset reference')
    substr = asm_str.split('(')
    if not len(substr) == 2:
        raise SyntaxError('Malformed GPR reference with offset')
    if not substr[0].isdigit():
        raise SyntaxError('Offset reference not a number')
    offset = int(substr[0])
    gpr = _get_single_gpr(substr[1][:-1].strip().lower())
    return gpr, offset

#############################################
#            Instruction Factory            #
#############################################


class InstructionFactory(object):

    def __init__(self, to_lower=False):
        # Mapping of mnemonics to instruction classes
        self.mnem_map = {}
        self.opcode_map = {}
        self.__register_mnemonics(GIns, to_lower)

    def __register_mnemonics(self, class_p, to_lower):
        """ Find all final classes derived from Ins and append their mnemonic and class type to dictionary"""
        for cls in class_p.__subclasses__():
            if len(cls.__subclasses__()) > 0:
                self.__register_mnemonics(cls, to_lower)
            else:
                if isinstance(cls.MNEM, str):
                    if cls.MNEM in self.mnem_map:
                        raise Exception('Error adding mnemonic \'' + cls.MNEM + '\' for class ' + cls.__name__
                                        + '. Mnemonic already in use.')
                    if (to_lower):
                        self.mnem_map.update({cls.MNEM.lower(): cls})
                    else:
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

#############################################
#            Bounds Checking                #
#############################################


def check_bounds_gpr_ref(gpr_ref):
    if not (0 <= gpr_ref < NUM_GPRS):
        raise SyntaxError('GPR reference out of bounds')


def check_bounds_wrd_ref(wrd_ref):
    if not (0 <= wrd_ref < NUM_WRDS):
        raise SyntaxError('WRD reference out of bounds')


def check_bounds_i_type_imm(imm):
    if not (0 <= imm < 2 ** I_TYPE_IMM_WIDTH):
        raise SyntaxError('imm out of bounds')


#############################################
#    Virtual Instruction Base Classes       #
#############################################


class GIns(object):
    """Generic instruction """

    CYCLES = 1

    def __init__(self, ctx):
        self.ctx = ctx
        self.malformed = False
        self.hex_str = 0

    @classmethod
    def from_assembly(cls, address, mnem, params, ctx):
        """Create instruction object from assembly string"""
        return cls.enc(address, mnem, params, ctx)

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        raise Exception('This method must be overridden in a derived class')

    def get_cycles(self):
        return self.CYCLES


class GInsBn(GIns):
    """Standard Bignum format BN.<ins> <wrd>, <wrs1>, <wrs2>, FG<flag_group> """

    def __init__(self, rd, rs1, rs2, flag_group, ctx):
        self.rd = rd
        self.rs1 = rs1
        self.rs2 = rs2
        self.flag_group = flag_group
        super().__init__(ctx)

    def exec_set_all_flags(self, res, m):
        if self.flag_group == 'standard':
            m.set_c_z_m_l(res)
        else:
            m.setx_c_z_m_l(res)

    def exec_set_zml_flags(self, res, m):
        if self.flag_group == 'standard':
            m.set_z_m_l(res)
        else:
            m.setx_z_m_l(res)

    def exec_get_carry(self, m):
        if self.flag_group == 'standard':
            return m.get_flag('C')
        else:
            return m.get_flag('XC')


class GInsBnShift(GInsBn):
    """Standard Bignum format with immediate shift
    BN.<ins> <wrd>, <wrs1>, <wrs2>, FG<flag_group> [, <shift_type> <shift_bytes>B]"""

    def __init__(self, rd, rs1, rs2, flag_group, shift_type, shift_bytes, ctx):
        self.shift_type = shift_type
        self.shift_bytes = shift_bytes
        super().__init__(rd, rs1, rs2, flag_group, ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' w' + str(self.rd) + ', w' + str(self.rs1) + ', w' + str(self.rs2)
        if self.shift_type == 'right':
            asm_str += ' >> ' + str(self.shift_bytes*8)
        else:
            if self.shift_bytes:
                asm_str += ' << ' + str(self.shift_bytes*8)
        if self.flag_group == 'extension':
            asm_str += ', FG1'
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        rd, rs1, rs2, shift_type, shift_bits, flag_group = _get_three_wdr_with_flag_group_and_shift(params)
        if shift_bits % 8:
            raise SyntaxError('Input shift immediate not byte aligned')
        return cls(rd, rs1, rs2, flag_group, shift_type, int(shift_bits/8), ctx.ins_ctx)

    def exec_shift(self, m):
        if self.shift_type == 'right':
            rs2op = (m.get_reg(self.rs2) >> self.shift_bytes*8) & m.xlen_mask
        else:
            rs2op = (m.get_reg(self.rs2) << self.shift_bytes*8) & m.xlen_mask
        return rs2op


class GInsBnCmpShift(GInsBn):
    """Bignum compare format with immediate shift
    BN.<ins> <wrs1>, <wrs2>, FG<flag_group> [, <shift_type> <shift_bytes>B]"""

    def __init__(self, rs1, rs2, flag_group, shift_type, shift_bytes, ctx):
        self.shift_type = shift_type
        self.shift_bytes = shift_bytes
        super().__init__(None, rs1, rs2, flag_group, ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' w' + str(self.rs1) + ', w' + str(self.rs2)
        if self.shift_type == 'right':
            asm_str += ' >> ' + str(self.shift_bytes*8)
        else:
            if self.shift_bytes:
                asm_str += ' << ' + str(self.shift_bytes*8)
        if self.flag_group == 'extension':
            asm_str += ', FG1'
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        rs1, rs2, shift_type, shift_bits, flag_group = _get_two_wdr_with_flag_group_and_shift(params)
        if shift_bits % 8:
            raise SyntaxError('Input shift immediate not byte aligned')
        return cls(rs1, rs2, flag_group, shift_type, int(shift_bits/8), ctx.ins_ctx)

    def exec_shift(self, m):
        if self.shift_type == 'right':
            rs2op = (m.get_reg(self.rs2) >> self.shift_bytes*8) & m.xlen_mask
        else:
            rs2op = (m.get_reg(self.rs2) << self.shift_bytes*8) & m.xlen_mask
        return rs2op


class GInsBnImm(GInsBn):
    """Standard Bignum format with one source register and immediate
    BN.<ins> <wrd>, <wrs>, <imm>, [ FG<flag_group>]"""

    def __init__(self, rd, rs, imm, flag_group, ctx):
        self.imm = imm
        super().__init__(rd, rs, None, flag_group, ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' w' + str(self.rd) + ', w' + str(self.rs1) + ', ' + str(self.imm)
        if self.flag_group == 'extension':
            asm_str += ', FG1'
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        rd, rs, imm, flag_group = _get_two_wdr_and_imm_with_flag_group(params)
        return cls(rd, rs, imm, flag_group, ctx.ins_ctx)


class GInsBnMod(GInsBn):
    """Standard Bignum format for pseudo modulo operations
    BN.<ins> <wrd>, <wrs1>, <wrs2>"""

    def __init__(self, rd, rs1, rs2, ctx):
        super().__init__(rd, rs1, rs2, None, ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' w' + str(self.rd) + ', w' + str(self.rs1) + ', w' + str(self.rs2)
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        rd, rs1, rs2, = _get_three_wdr(params)
        return cls(rd, rs1, rs2, ctx.ins_ctx)


class GInsIndReg(GIns):
    """Standard Bignum format for indirect move: BN.<ins> x<GPR>[++], x<GPR>[++] """

    def __init__(self, xd, inc_xd, xs, inc_xs, ctx):
        self.xd = xd
        self.inc_xd = inc_xd
        self.xs = xs
        self.inc_xs = inc_xs
        if inc_xd and inc_xs:
            raise SyntaxError("Only one increment allowed in indirect instructions")
        super().__init__(ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' x' + str(self.xd)
        if self.inc_xd:
            asm_str += '++'
        asm_str += ', x' + str(self.xs)
        if self.inc_xs:
            asm_str += '++'
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        xd, inc_xd, xs, inc_xs = _get_two_gprs_with_inc(params)
        return cls(xd, inc_xd, xs, inc_xs, ctx.ins_ctx)


class GInsIndLs(GIns):
    """Standard Bignum format for indirect load, store : BN.<ins> <gpr>[<inc>], <offset>(<gpr>[<gpr_inc>]) """

    def __init__(self, x1, inc_x1, x2, inc_x2, offset, ctx):
        self.x1 = x1
        self.inc_x1 = inc_x1
        self.x2 = x2
        self.inc_x2 = inc_x2
        self.offset = offset
        if inc_x1 and inc_x2:
            raise SyntaxError("Only one increment allowed in indirect instructions")
        super().__init__(ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' x' + str(self.x1)
        if self.inc_x1:
            asm_str += '++'
        asm_str += ', ' + str(self.offset) + '(x' + str(self.x2)
        if self.inc_x2:
            asm_str += '++'
        asm_str += ')'
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        x1, inc_x1, x2, inc_x2, offset = _get_two_gprs_with_inc_and_offset(params)
        return cls(x1, inc_x1, x2, inc_x2, offset, ctx.ins_ctx)


class GInsWsr(GIns):
    """WSR type"""

    def __init__(self, wrd, wsr, wrs, ctx):
        self.wrd = wrd
        self.wsr = wsr
        self.wrs = wrs
        super().__init__(ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' w' + str(self.wrd) + ', ' + str(self.wsr) + ', w' + str(self.wrs)
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        wrd, imm, wrs = _get_wdr_imm_wd(params)
        check_bounds_wrd_ref(wrd)
        check_bounds_wrd_ref(wrs)
        # todo: check bounds of immediate
        return cls(wrd, imm, wrs, ctx.ins_ctx)


#############################################
#              Arithmetic                   #
#############################################

class IBnAdd(GInsBnShift):
    """Add instruction with one shifted input"""

    MNEM = 'BN.ADD'

    def __init__(self, rd, rs1, rs2, flag_group, shift_type, shift_bytes, ctx):
        super().__init__(rd, rs1, rs2, flag_group, shift_type, shift_bytes, ctx)

    def get_asm_str(self):
        return super().get_asm_str()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        return super().enc(addr, mnem, params, ctx)

    def execute(self, m):
        global debug_cnt
        rs2op = self.exec_shift(m)
        res = m.get_reg(self.rs1) + rs2op
        self.exec_set_all_flags(res, m)
        m.set_reg(self.rd, res & m.xlen_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnSub(GInsBnShift):
    """Sub instruction with one shifted input"""

    MNEM = 'BN.SUB'

    def __init__(self, rd, rs1, rs2, flag_group, shift_type, shift_bytes, ctx):
        super().__init__(rd, rs1, rs2, flag_group, shift_type, shift_bytes, ctx)

    def get_asm_str(self):
        return super().get_asm_str()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        return super().enc(addr, mnem, params, ctx)

    def execute(self, m):
        rs2op = self.exec_shift(m)
        res = (m.get_reg(self.rs1) - rs2op)
        self.exec_set_all_flags(res, m)
        m.set_reg(self.rd, res  & m.xlen_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnCmp(GInsBnCmpShift):
    """Cmp instruction with one shifted input"""

    MNEM = 'BN.CMP'

    def __init__(self, rs1, rs2, flag_group, shift_type, shift_bytes, ctx):
        super().__init__(rs1, rs2, flag_group, shift_type, shift_bytes, ctx)

    def get_asm_str(self):
        return super().get_asm_str()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        return super().enc(addr, mnem, params, ctx)

    def execute(self, m):
        rs2op = self.exec_shift(m)
        res = (m.get_reg(self.rs1) - rs2op)
        self.exec_set_all_flags(res, m)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnAddc(GInsBnShift):
    """Add with carry instruction with one shifted input"""

    MNEM = 'BN.ADDC'

    def __init__(self, rd, rs1, rs2, flag_group, shift_type, shift_bytes, ctx):
        super().__init__(rd, rs1, rs2, flag_group, shift_type, shift_bytes, ctx)

    def get_asm_str(self):
        return super().get_asm_str()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        return super().enc(addr, mnem, params, ctx)

    def execute(self, m):
        rs2op = self.exec_shift(m)
        res = (m.get_reg(self.rs1) + rs2op + int(self.exec_get_carry(m)))
        self.exec_set_all_flags(res, m)
        m.set_reg(self.rd, res & m.xlen_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnSubb(GInsBnShift):
    """Sub with borrow instruction with one shifted input"""

    MNEM = 'BN.SUBB'

    def __init__(self, rd, rs1, rs2, flag_group, shift_type, shift_bytes, ctx):
        super().__init__(rd, rs1, rs2, flag_group, shift_type, shift_bytes, ctx)

    def get_asm_str(self):
        return super().get_asm_str()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        return super().enc(addr, mnem, params, ctx)

    def execute(self, m):
        rs2op = self.exec_shift(m)
        res = (m.get_reg(self.rs1) - rs2op - int(self.exec_get_carry(m)))
        self.exec_set_all_flags(res, m)
        m.set_reg(self.rd, res & m.xlen_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnCmpb(GInsBnCmpShift):
    """Cmp with borrow instruction with one shifted input"""

    MNEM = 'BN.CMPB'

    def __init__(self, rs1, rs2, flag_group, shift_type, shift_bytes, ctx):
        super().__init__(rs1, rs2, flag_group, shift_type, shift_bytes, ctx)

    def get_asm_str(self):
        return super().get_asm_str()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        return super().enc(addr, mnem, params, ctx)

    def execute(self, m):
        rs2op = self.exec_shift(m)
        res = (m.get_reg(self.rs1) - rs2op - int(self.exec_get_carry(m)))
        self.exec_set_all_flags(res, m)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnAddi(GInsBnImm):
    """Add with immediate"""

    MNEM = 'BN.ADDI'

    def __init__(self, rd, rs, imm, flag_group, ctx):
        super().__init__(rd, rs, imm, flag_group, ctx)

    def get_asm_str(self):
        return super().get_asm_str()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        return super().enc(addr, mnem, params, ctx)

    def execute(self, m):
        res = (m.get_reg(self.rs1) + self.imm)
        self.exec_set_all_flags(res, m)
        m.set_reg(self.rd, res & m.xlen_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnSubi(GInsBnImm):
    """Sub with immediate"""

    MNEM = 'BN.SUBI'

    def __init__(self, rd, rs, imm, flag_group, ctx):
        super().__init__(rd, rs, imm, flag_group, ctx)

    def get_asm_str(self):
        return super().get_asm_str()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        return super().enc(addr, mnem, params, ctx)

    def execute(self, m):
        res = (m.get_reg(self.rs1) - self.imm)
        self.exec_set_all_flags(res, m)
        m.set_reg(self.rd, res & m.xlen_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnAddm(GInsBnMod):
    """Pseudo modular add"""

    MNEM = 'BN.ADDM'

    def __init__(self, rd, rs1, rs2, ctx):
        super().__init__(rd, rs1, rs2, ctx)

    def get_asm_str(self):
        return super().get_asm_str()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        return super().enc(addr, mnem, params, ctx)

    def execute(self, m):
        res = (m.get_reg(self.rs1) + m.get_reg(self.rs2))
        if res >= m.get_reg('mod'):
            res = res - m.get_reg('mod')
        m.set_reg(self.rd, res & m.xlen_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnSubm(GInsBnMod):
    """Pseudo modular sub"""

    MNEM = 'BN.SUBM'

    def __init__(self, rd, rs1, rs2, ctx):
        super().__init__(rd, rs1, rs2, ctx)

    def get_asm_str(self):
        return super().get_asm_str()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        return super().enc(addr, mnem, params, ctx)

    def execute(self, m):
        res = m.get_reg(self.rs1) - m.get_reg(self.rs2)
        if res < 0:
            res = m.get_reg('mod') + res
        m.set_reg(self.rd, res & m.xlen_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class GInsBnMulqacc(GInsBn):
    """Quarter-word Multiply and Accumulate base instruction"""

    def __init__(self, wrd, wrd_hw_sel, wrs1, wrs1_qw_sel, wrs2, wrs2_qw_sel, acc_shift_imm, ctx):
        self.wrd_hw_sel = wrd_hw_sel
        self.wrs1_qw_sel = wrs1_qw_sel
        self.wrs2_qw_sel = wrs2_qw_sel
        self.imm = acc_shift_imm
        super().__init__(wrd, wrs1, wrs2, None, ctx)

    def get_asm_str(self):
        asm_str = self.MNEM
        if self.rd is not None:
            asm_str +=  ' w' + str(self.rd)
            if self.wrd_hw_sel == 'upper':
                asm_str += 'U'
            else:
                asm_str += 'L'
        asm_str += ', w' + str(self.rs1) + '.' + str(self.wrs1_qw_sel)
        asm_str += ', w' + str(self.rs2) + '.' + str(self.wrs2_qw_sel)
        asm_str += ', ' + str(self.imm)
        return self.hex_str, asm_str, self.malformed


class IBnMulqacc(GInsBnMulqacc):
    """Quarter-word Multiply and Accumulate
    BN.MULQACC <wrs1>.<wrs1_qwsel>, <wrs2>.<wrs2_qwsel>, <acc_shift_imm>"""

    MNEM = 'BN.MULQACC'

    def execute(self, m):
        op1 = m.get_reg_qw(self.rs1, self.wrs1_qw_sel)
        op2 = m.get_reg_qw(self.rs2, self.wrs2_qw_sel)
        res = (op1*op2) << self.imm
        m.set_acc(m.get_acc() + res)
        trace_str = self.get_asm_str()[1]
        return trace_str, None

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        wrs1, wrs1_qw_sel, wrs2, wrs2_qw_sel, acc_shift_imm = \
            _get_two_wdr_with_quadw_sel_and_imm(params)
        return cls(None, None, wrs1, wrs1_qw_sel, wrs2, wrs2_qw_sel, acc_shift_imm, ctx.ins_ctx)


class IBnMulqaccZ(GInsBnMulqacc):
    """Quarter-word Multiply and Accumulate
    BN.MULQACC <wrs1>.<wrs1_qwsel>, <wrs2>.<wrs2_qwsel>, <acc_shift_imm>"""

    MNEM = 'BN.MULQACC.Z'

    def execute(self, m):
        m.set_acc(0)
        op1 = m.get_reg_qw(self.rs1, self.wrs1_qw_sel)
        op2 = m.get_reg_qw(self.rs2, self.wrs2_qw_sel)
        res = (op1*op2) << (self.imm * 64)
        m.set_acc(m.get_acc() + res)
        trace_str = self.get_asm_str()[1]
        return trace_str, None

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        wrs1, wrs1_qw_sel, wrs2, wrs2_qw_sel, acc_shift_imm = \
            _get_two_wdr_with_quadw_sel_and_imm(params)
        return cls(None, None, wrs1, wrs1_qw_sel, wrs2, wrs2_qw_sel, acc_shift_imm, ctx.ins_ctx)


class IBnMulqaccSo(GInsBnMulqacc):
    """Quarter-word Multiply and Accumulate
    BN.MULQACC <wrs1>.<wrs1_qwsel>, <wrs2>.<wrs2_qwsel>, <acc_shift_imm>"""

    MNEM = 'BN.MULQACC.SO'

    def execute(self, m):
        op1 = m.get_reg_qw(self.rs1, self.wrs1_qw_sel)
        op2 = m.get_reg_qw(self.rs2, self.wrs2_qw_sel)
        res = (op1*op2) << self.imm
        m.set_acc(m.get_acc() + res)
        shift_out = m.get_acc() & m.hw_mask
        m.set_acc(m.get_acc() >> m.hw_width)
        if self.wrd_hw_sel == 'lower':
            m.set_reg_half_word(self.rd, 0, shift_out)
        elif self.wrd_hw_sel == 'upper':
            m.set_reg_half_word(self.rd, 1, shift_out)
        else:
            raise SyntaxError('Illegal half word indicator')
        trace_str = self.get_asm_str()[1]
        return trace_str, None

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        wrd, wrd_hw_sel, wrs1, wrs1_qw_sel, wrs2, wrs2_qw_sel, acc_shift_imm = \
            _get_wdr_with_halfw_sel_two_wdr_with_quadw_sel_and_imm(params)
        return cls(wrd, wrd_hw_sel, wrs1, wrs1_qw_sel, wrs2, wrs2_qw_sel, acc_shift_imm, ctx.ins_ctx)


class IBnMulh(GInsBn):
    """Half Word Multiply
    BN.MULH <rd>, <rs1>[L|U], <rs2>[L|U]"""

    MNEM = 'BN.MULH'

    def __init__(self, rd, rs1, rs1_hw_sel, rs2, rs2_hw_sel, ctx):
        self.rs1_hw_sel = rs1_hw_sel
        self.rs2_hw_sel = rs2_hw_sel
        super().__init__(rd, rs1, rs2, None, ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' w' + str(self.rd) + ', w' + str(self.rs1)
        if self.rs1_hw_sel == 'upper':
            asm_str += '.U'
        else:
            asm_str += '.L'
        asm_str += ', w' + str(self.rs2)
        if self.rs2_hw_sel == 'upper':
            asm_str += '.U'
        else:
            asm_str += '.L'
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        rd, rs1, rs1_hw_sel, rs2, rs2_hw_sel = _get_three_wdr_with_two_half_word_sels(params)
        return cls(rd, rs1, rs1_hw_sel, rs2, rs2_hw_sel, ctx.ins_ctx)

    def execute(self, m):
        if self.rs1_hw_sel == 'upper':
            op1 = (m.get_reg(self.rs1) >> int(m.XLEN/2)) & m.half_xlen_mask
        else:
            op1 = m.get_reg(self.rs1) & m.half_xlen_mask
        if self.rs2_hw_sel == 'upper':
            op2 = (m.get_reg(self.rs2) >> int(m.XLEN/2)) & m.half_xlen_mask
        else:
            op2 = m.get_reg(self.rs2) & m.half_xlen_mask
        res = op1*op2
        m.set_reg(self.rd, res)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


#############################################
#      Logical, select, shift, compare      #
#############################################


class IBnAnd(GInsBnShift):
    """And instruction with one shifted input"""

    MNEM = 'BN.AND'

    def __init__(self, rd, rs1, rs2, flag_group, shift_type, shift_bytes, ctx):
        super().__init__(rd, rs1, rs2, 'standard', shift_type, shift_bytes, ctx)

    def get_asm_str(self):
        return super().get_asm_str()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        return super().enc(addr, mnem, params, ctx)

    def execute(self, m):
        rs2op = self.exec_shift(m)
        res = (m.get_reg(self.rs1) & rs2op) & m.xlen_mask
        self.exec_set_zml_flags(res, m)
        m.set_reg(self.rd, res)
        # trace_str = self.get_asm_str()[1]
        trace_str = self.get_asm_str()[1] + "\n" + m.print_reg(self.rd)
        return trace_str, None


class IBnOr(GInsBnShift):
    """Or instruction with one shifted input"""

    MNEM = 'BN.OR'

    def __init__(self, rd, rs1, rs2, flag_group, shift_type, shift_bytes, ctx):
        super().__init__(rd, rs1, rs2, 'standard', shift_type, shift_bytes, ctx)

    def get_asm_str(self):
        return super().get_asm_str()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        return super().enc(addr, mnem, params, ctx)

    def execute(self, m):
        rs2op = self.exec_shift(m)
        res = (m.get_reg(self.rs1) | rs2op) & m.xlen_mask
        self.exec_set_zml_flags(res, m)
        m.set_reg(self.rd, res)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnXor(GInsBnShift):
    """Or instruction with one shifted input"""

    MNEM = 'BN.XOR'

    def __init__(self, rd, rs1, rs2, flag_group, shift_type, shift_bytes, ctx):
        super().__init__(rd, rs1, rs2, 'standard', shift_type, shift_bytes, ctx)

    def get_asm_str(self):
        return super().get_asm_str()

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        return super().enc(addr, mnem, params, ctx)

    def execute(self, m):
        rs2op = self.exec_shift(m)
        res = (m.get_reg(self.rs1) ^ rs2op) & m.xlen_mask
        self.exec_set_zml_flags(res, m)
        m.set_reg(self.rd, res)
        trace_str = self.get_asm_str()[1]
        return trace_str, None



class IBnNot(GIns):
    """Not instruction with one shifted input"""

    MNEM = 'BN.NOT'

    def __init__(self, rd, rs, shift_type, shift_bytes, ctx):
        self.rd = rd
        self.rs = rs
        self.shift_type = shift_type
        self.shift_bytes = shift_bytes
        super().__init__(ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' w' + str(self.rd) + ', w' + str(self.rs)
        if self.shift_type == 'right':
            asm_str += ' >> ' + str(self.shift_bytes*8)
        else:
            if self.shift_bytes:
                asm_str += ' << ' + str(self.shift_bytes*8)
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        rd, rs, shift_type, shift_bits = _get_two_wdr_with_shift(params)
        if shift_bits % 8:
            raise SyntaxError('Input shift immediate not byte aligned')
        return cls(rd, rs, shift_type, int(shift_bits / 8), ctx.ins_ctx)

    def execute(self, m):
        if self.shift_type == 'right':
            rs2op = (m.get_reg(self.rs) >> self.shift_bytes*8) & m.xlen_mask
        else:
            rs2op = (m.get_reg(self.rs) << self.shift_bytes*8) & m.xlen_mask
        res = (~rs2op) & m.xlen_mask
        self.exec_set_zml_flags(res, m)
        m.set_reg(self.rd, res)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnRshi(GInsBn):
    """Concatenate and Right shift"""

    MNEM = 'BN.RSHI'

    def __init__(self, rd, rs1, rs2, shift_bits, ctx):
        self.shift_bits = shift_bits
        super().__init__(rd, rs1, rs2, None, ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' w' + str(self.rd) + ', w' + str(self.rs1) + ', w' + str(self.rs2)
        asm_str += ' >> ' + str(self.shift_bits)
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        rd, rs1, rs2, shift_type, shift_bits, flag_group = _get_three_wdr_with_flag_group_and_shift(params)
        if shift_type != 'right':
            raise SyntaxError('Only right shift possible with this instruction')
        if flag_group != 'standard':
            raise SyntaxError('Only standard flag group possible with this instruction')
        return cls(rd, rs1, rs2, shift_bits, ctx.ins_ctx)

    def execute(self, m):
        conc = (m.get_reg(self.rs2) << m.XLEN) + m.get_reg(self.rs1)
        res = (conc >> self.shift_bits) & m.xlen_mask
        m.set_reg(self.rd, res)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnSel(GInsBn):
    """Select by flag"""

    MNEM = 'BN.SEL'

    def __init__(self, rd, rs1, rs2, flag_group, flag, ctx):
        self.flag = flag
        super().__init__(rd, rs1, rs2, flag_group, ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' w' + str(self.rd) + ', w' + str(self.rs1) + ', w' + str(self.rs2) + ', '
        if self.flag_group == 'extension':
            asm_str += 'FG1.'
        asm_str += self.flag.upper()
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        rd, rs1, rs2, flag_group, flag = _get_three_wdr_with_flag_group_and_flag(params)
        return cls(rd, rs1, rs2, flag_group, flag, ctx.ins_ctx)

    def execute(self, m):
        flag_id = self.flag.upper()
        if self.flag_group == 'extension':
            flag_id = 'X' + flag_id
        flag_val = m.get_flag(flag_id)
        res = m.get_reg(self.rs1) if flag_val else m.get_reg(self.rs2)
        m.set_reg(self.rd, res)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


#############################################
#            Load/Store/Move                #
#############################################

class IBnMov(GIns):
    """Direct move instruction"""

    MNEM = 'BN.MOV'

    def __init__(self, rd, rs, ctx):
        self.rd = rd
        self.rs = rs
        super().__init__(ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' w' + str(self.rd) + ', w' + str(self.rs)
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        rd, rs = _get_two_wdr(params)
        return cls(rd, rs, ctx.ins_ctx)

    def execute(self, m):
        m.set_reg(self.rd, m.get_reg(self.rs))
        # print(m.get_gprs())
        trace_str = self.get_asm_str()[1] + "\n" + m.print_reg(self.rd)
        return trace_str, None


class IBnMovr(GInsIndReg):
    """Indirect move instruction"""

    MNEM = 'BN.MOVR'

    def __init__(self, xd, inc_xd, xs, inc_xs, ctx):
        super().__init__(xd, inc_xd, xs, inc_xs, ctx)

    def execute(self, m):
        dst_wdr = m.get_gpr(self.xd)
        src_wdr = m.get_gpr(self.xs)
        m.set_reg(dst_wdr, m.get_reg(src_wdr))
        if self.inc_xd:
            m.inc_gpr(self.xd)
        if self.inc_xs:
            m.inc_gpr(self.xs)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnLid(GInsIndLs):
    """Indirect load instruction"""

    MNEM = 'BN.LID'

    def __init__(self, x1, inc_x1, x2, inc_x2, offset, ctx):
        super().__init__(x1, inc_x1, x2, inc_x2, offset, ctx)

    def execute(self, m):

        dst_wdr = m.get_gpr(self.x1)
        dmem_addr = self.offset + (m.get_gpr(self.x2))
        if (self.ctx.dmem_byte_addressing):
            dmem_addr = dmem_addr // 32
        m.set_reg(dst_wdr, m.get_dmem(dmem_addr))
        if self.inc_x1:
            m.inc_gpr(self.x1)
        if self.inc_x2:
            if (self.ctx.dmem_byte_addressing):
                m.inc_gpr_wlen_bytes(self.x2)
            else:
                m.inc_gpr(self.x2)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnSid(GInsIndLs):
    """Indirect store instruction"""

    MNEM = 'BN.SID'

    def __init__(self, x1, inc_x1, x2, inc_x2, offset, ctx):
        super().__init__(x1, inc_x1, x2, inc_x2, offset, ctx)

    def execute(self, m):
        src_wdr = m.get_gpr(self.x1)
        dmem_addr = self.offset + (m.get_gpr(self.x2))
        if (self.ctx.dmem_byte_addressing):
            dmem_addr = dmem_addr // 32
        m.set_dmem(dmem_addr, m.get_reg(src_wdr))
        if self.inc_x1:
            m.inc_gpr(self.x1)
        if self.inc_x2:
            if (self.ctx.dmem_byte_addressing):
                m.inc_gpr_wlen_bytes(self.x2)
            else:
                m.inc_gpr(self.x2)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnWsrrs(GInsWsr):
    """Atomic Read and Set Bits in WSR"""

    MNEM = 'BN.WSRRS'

    def execute(self, m):
        wsr_val = m.get_wsr(self.wsr)
        m.set_reg(self.wrd, wsr_val)
        wsr_new = wsr_val | m.get_reg(self.wrs)
        m.set_wsr(self.wsr, wsr_new)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IBnWsrrw(GInsWsr):
    """Atomic Read/Write WSR"""

    MNEM = 'BN.WSRRW'

    def execute(self, m):
        wsr_val = m.get_wsr(self.wsr)
        m.set_reg(self.wrd, wsr_val)
        wsr_new = m.get_reg(self.wrs)
        m.set_wsr(self.wsr, wsr_new)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


#############################################
#              Flow Control                 #
#############################################

class IOtLoopi(GIns):
    """Immediate Loop"""

    MNEM = 'LOOPI'

    def __init__(self, iter, len, ctx):
        self.iter = iter
        self.len = len
        super().__init__(ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' ' + str(self.iter) + ', ' + str(self.len)
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        iter, size = _get_two_imm(params)
        return cls(iter, size, ctx.ins_ctx)

    def execute(self, m):
        m.push_loop_stack(self.iter - 1, self.len + m.get_pc(), m.get_pc() + 1)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtLoop(GIns):
    """Indirect Loop"""

    MNEM = 'LOOP'

    def __init__(self, xiter, len, ctx):
        self.xiter = xiter  # GPR containing # of iterations
        self.len = len
        super().__init__(ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' x' + str(self.xiter) + ', ' + str(self.len)
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        gpr, len = _get_gpr_and_optional_imm(params)
        cl_addr = ctx.get_loop_close_addr(addr)
        if not cl_addr and not len:
            raise SyntaxError('No \'loopend\' pseudo instruction found and no length immediate in loop instruction.'
                              ' One must be provided.')
        if len and cl_addr:
            len_from_pseudo = cl_addr - addr - 1
            if len != len_from_pseudo:
                raise SyntaxError('Mismatch between loop length immediate and calculated length with '
                                  '\'loopend\' pseudo instruction')
        if not len:
            len = len_from_pseudo
        return cls(gpr, len, ctx.ins_ctx)

    def execute(self, m):
        iter = m.get_gpr(self.xiter)
        m.push_loop_stack(iter - 1, self.len + m.get_pc(), m.get_pc() + 1)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


#############################################
#          RV derived instructions          #
#############################################

class IOtGpr(GIns):
    """RV based instructions format with one dest and two src GPRs"""

    def __init__(self, xd, xs1, xs2, ctx):
        self.xd = xd
        self.xs1 = xs1
        self.xs2 = xs2
        super().__init__(ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' x' + str(self.xd) + ', x' + str(self.xs1) + ', x' + str(self.xs2)
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        xd, xs1, xs2 = _get_three_gprs(params)
        check_bounds_gpr_ref(xd)
        check_bounds_gpr_ref(xs1)
        check_bounds_gpr_ref(xs2)
        return cls(xd, xs1, xs2, ctx.ins_ctx)

    def execute(self, m):
        res = m.get_gpr(self.xs1) + m.get_gpr(self.xs2)
        m.set_gpr(self.xd, res & m.gpr_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtImm(GIns):
    """RV based instructions format with one dest and one src GPR + immediate"""

    def __init__(self, xd, xs, imm, ctx):
        self.xd = xd
        self.xs = xs
        self.imm = imm
        super().__init__(ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' x' + str(self.xd) + ', x' + str(self.xs) + ', ' + str(self.imm)
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        xd, xs, imm = _get_two_gprs_with_imm(params)
        check_bounds_gpr_ref(xd)
        check_bounds_gpr_ref(xs)
        check_bounds_i_type_imm(imm)
        return cls(xd, xs, imm, ctx.ins_ctx)


class IOtBranch(GIns):
    """Branch type"""

    def __init__(self, grs1, grs2, offset, addr, ctx, label=None):
        self.grs1 = grs1
        self.grs2 = grs2
        self.offset = offset
        self.addr = addr
        self.label = label
        super().__init__(ctx)

    def get_asm_str(self):
        target = self.offset + self.addr
        asm_str = self.MNEM + ' x' + str(self.grs1) + ', x' + str(self.grs2) + ', ' \
                  + self.ctx.get_or_add_label(target)
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        gpr1, gpr2, func_label = _get_two_gprs_and_label(params)
        offset = ctx.get_addr_for_label(func_label) - addr
        check_bounds_gpr_ref(gpr1)
        check_bounds_gpr_ref(gpr2)
        return cls(gpr1, gpr2, offset, addr, ctx.ins_ctx, label=func_label)


class IOtCsr(GIns):
    """CSR type"""

    def __init__(self, grd, csr, grs, ctx):
        self.grd = grd
        self.csr = csr
        self.grs = grs
        super().__init__(ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' x' + str(self.grd) + ', ' + str(self.csr) + ', x' + str(self.grs)
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        grd, imm, grs = _get_gpr_imm_gpr(params)
        check_bounds_gpr_ref(grd)
        check_bounds_gpr_ref(grs)
        # todo: check bounds of immediate
        return cls(grd, imm, grs, ctx.ins_ctx)


class IOtAdd(IOtGpr):
    """Base add"""

    MNEM = 'ADD'

    def execute(self, m):
        res = m.get_gpr(self.xs1) + m.get_gpr(self.xs2)
        m.set_gpr(self.xd, res & m.gpr_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtAddi(IOtImm):
    """Base add immediate"""

    MNEM = 'ADDI'

    def execute(self, m):
        res = m.get_gpr(self.xs) + self.imm
        m.set_gpr(self.xd, res & m.gpr_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtSub(IOtGpr):
    """Base subtract"""

    MNEM = 'SUB'

    def execute(self, m):
        res = m.get_gpr(self.xs1) - m.get_gpr(self.xs2)
        m.set_gpr(self.xd, res & m.gpr_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtAnd(IOtGpr):
    """Base bitwise AND"""

    MNEM = 'AND'

    def execute(self, m):
        res = m.get_gpr(self.xs1) & m.get_gpr(self.xs2)
        m.set_gpr(self.xd, res & m.gpr_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtAndi(IOtImm):
    """Base bitwise AND with immediate"""

    MNEM = 'ANDI'

    def execute(self, m):
        res = m.get_gpr(self.xs) & self.imm
        m.set_gpr(self.xd, res & m.gpr_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtOr(IOtGpr):
    """Base bitwise OR"""

    MNEM = 'OR'

    def execute(self, m):
        res = m.get_gpr(self.xs1) | m.get_gpr(self.xs2)
        m.set_gpr(self.xd, res & m.gpr_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtOri(IOtImm):
    """Base bitwise OR with immediate"""

    MNEM = 'ORI'

    def execute(self, m):
        res = m.get_gpr(self.xs) | self.imm
        m.set_gpr(self.xd, res & m.gpr_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtXor(IOtGpr):
    """Base bitwise XOR"""

    MNEM = 'XOR'

    def execute(self, m):
        res = m.get_gpr(self.xs1) ^ m.get_gpr(self.xs2)
        m.set_gpr(self.xd, res & m.gpr_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtXori(IOtImm):
    """Base bitwise XOR with immediate"""

    MNEM = 'XORI'

    def execute(self, m):
        res = m.get_gpr(self.xs) ^ self.imm
        m.set_gpr(self.xd, res & m.gpr_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtSlli(IOtImm):
    """Left shift immediate"""

    MNEM = 'SLLI'

    def execute(self, m):
        res = m.get_gpr(self.xs) << self.imm
        m.set_gpr(self.xd, res & m.gpr_mask)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtJal(GIns):
    """Jump and link"""

    MNEM = 'JAL'

    def __init__(self, xd, imm, addr, ctx, label=None):
        self.xd = xd
        self.imm = imm
        self.addr = addr
        self.label = label
        super().__init__(ctx)

    def get_asm_str(self):
        target = self.imm + self.addr
        asm_str = self.MNEM + ' x' + str(self.xd) + ', ' + self.ctx.get_or_add_label(target)
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        gpr, func_label = _get_gpr_and_label(params)
        imm = ctx.get_addr_for_label(func_label) - addr
        check_bounds_gpr_ref(gpr)
        return cls(gpr, imm, addr, ctx.ins_ctx, label=func_label)

    def execute(self, m):
        m.set_gpr(self.xd, m.get_pc() + 1)
        jump_target = m.get_pc() + self.imm
        trace_str = self.get_asm_str()[1]
        return trace_str, jump_target


class IOtJalr(IOtImm):
    """Jump and link register"""

    MNEM = 'JALR'

    def execute(self, m):
        m.set_gpr(self.xd, m.get_pc())
        try:
            jump_target = m.get_gpr(self.xs) + self.imm
        except CallStackUnderrun:
            if m.get_pc() == m.stop_addr:
                # We have an underrun but are at the stop address anyways, so this is fine
                jump_target = m.get_pc()
            else:
                m.finish()
                jump_target = m.get_pc()

        trace_str = self.get_asm_str()[1]
        return trace_str, jump_target


class IOtEcall(GIns):
    """ECALL instruction"""

    MNEM = 'ECALL'

    def __init__(self, addr, ctx, label=None):
        self.addr = addr
        super().__init__(ctx)

    def get_asm_str(self):
        asm_str = self.MNEM
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        return cls(addr, ctx.ins_ctx)

    def execute(self, m):
        m.finish(breakpoint=False)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtBne(IOtBranch):
    """Branch not equal"""

    MNEM = 'BNE'

    def execute(self, m):
        branch_target = None
        if m.get_gpr(self.grs1) != m.get_gpr(self.grs2):
            branch_target = m.get_pc() + self.offset
        trace_str = self.get_asm_str()[1]
        return trace_str, branch_target


class IOtBeq(IOtBranch):
    """Branch equal"""

    MNEM = 'BEQ'

    def execute(self, m):
        branch_target = None
        branch = m.get_gpr(self.grs1) == m.get_gpr(self.grs2)
        if branch:
            branch_target = m.get_pc() + self.offset
        trace_str = self.get_asm_str()[1]
        return trace_str, branch_target


class IOtCsrrs(IOtCsr):
    """Atomic Read and Set Bits in CSR"""

    MNEM = 'CSRRS'

    def execute(self, m):
        csr_val = m.get_csr(self.csr)
        m.set_gpr(self.grd, csr_val)
        csr_new = csr_val | m.get_gpr(self.grs)
        m.set_csr(self.csr, csr_new)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtCsrrw(IOtCsr):
    """Atomic Read/Write CSR"""

    MNEM = 'CSRRW'

    def execute(self, m):
        csr_val = m.get_csr(self.csr)
        m.set_gpr(self.grd, csr_val)
        csr_new = m.get_gpr(self.grs)
        m.set_csr(self.csr, csr_new)
        trace_str = self.get_asm_str()[1]
        return trace_str, None


class IOtLui(GIns):
    """Load upper immediate"""

    MNEM = 'LUI'

    def __init__(self, grd, imm, ctx):
        self.grd = grd
        self.imm = imm
        super().__init__(ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' x' + str(self.grd) + ', ' + str(self.imm)
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        grd, imm = _get_gpr_and_imm(params)
        return cls(grd, imm, ctx.ins_ctx)

    def execute(self, m):
        grp_low_12_bits = m.get_gpr(self.grd) & 2**12-1
        new_val = (self.imm << 12) + grp_low_12_bits
        m.set_gpr(self.grd, new_val)
        trace_str = self.get_asm_str()[1]
        return trace_str, None

class IOtLw(GIns):
    """Load word"""

    MNEM = 'LW'

    def __init__(self, grd, offset, grs, ctx):
        self.grd = grd
        self.offset = offset
        self.grs = grs
        super().__init__(ctx)

    def get_asm_str(self):
        asm_str = self.MNEM + ' x' + str(self.grd) + ', ' + str(self.offset) + '(' + str(self.grs) + ')'
        return self.hex_str, asm_str, self.malformed

    @classmethod
    def enc(cls, addr, mnem, params, ctx):
        grd, offset, grs = _get_two_gprs_with_offset(params)
        return cls(grd, offset, grs, ctx.ins_ctx)

    def execute(self, m):
        m.set_gpr(self.grd, m.get_dmem_otbn(m.get_gpr(self.grs)+self.offset))
        trace_str = self.get_asm_str()[1]
        return trace_str, None


if __name__ == "__main__":
    raise Exception('This file is not executable')