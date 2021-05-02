include "vt_consts.dfy"
include "bv_ops.dfy"

module vt_types {
    import opened vt_consts
    import opened bv_ops

    type reg_index = uint5

    datatype reg32_t = GPR(index: reg_index)

    datatype reg256_t =
        | WDR(index: reg_index)
        | WMOD // Wide modulo register
        | WRND // Wide random number
        | WACC // Wide accumulator

    predicate is_wide_data_register(r: reg256_t)
    {
        r.WDR?
    }

    datatype ins32 =
        | ADD(xrd: reg32_t, xrs1: reg32_t, xrs2: reg32_t)
        | ADDI(xrd: reg32_t, xrs1: reg32_t, imm: uint32)
        | LUI(xrd: reg32_t, imm: uint32)
        | SUB(xrd: reg32_t, xrs1: reg32_t, xrs2: reg32_t)
        | AND(xrd: reg32_t, xrs1: reg32_t, xrs2: reg32_t)
        | ANDI(xrd: reg32_t, xrs1: reg32_t, imm: uint32)
        | OR(xrd: reg32_t, xrs1: reg32_t, xrs2: reg32_t)
        | ORI(xrd: reg32_t, xrs1: reg32_t, imm: uint32)
        | XOR(xrd: reg32_t, xrs1: reg32_t, xrs2: reg32_t)
        | XORI(xrd: reg32_t, xrs1: reg32_t, imm: uint32)
        | LW(xrd: reg32_t, xrs1: reg32_t, imm: uint32)
        | SW(xrs1: reg32_t, xrs2: reg32_t, imm: uint32)
        | BEQ(xrs1: reg32_t, xrs2: reg32_t, offset: uint32)
        | BNE(xrs1: reg32_t, xrs2: reg32_t, offset: uint32)
        | LOOP(grs: reg32_t, bodysize: uint32)
        | LOOPI(iterations: uint32, bodysize: uint32)
        | JAL(xrd: reg32_t, offset: uint32)
        | JALR(xrd: reg32_t, xrs1: reg32_t, offset: uint32)
        | CSRRS(xrd: reg32_t, csr: reg32_t, xrs2: reg32_t)
        | CSRRW(xrd: reg32_t, csr: reg32_t, xrs2: reg32_t)
        | ECALL // TODO

    datatype ins256 =
        | BN_ADD(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        | BN_ADDC(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        | BN_ADDI(wrd: reg256_t, wrs1: reg256_t, imm: uint256, fg: uint1)
        | BN_ADDM(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t)
        | BN_MULQACC(zero: bool, wrs1: reg256_t, qwsel1: uint32, wrs2: reg256_t, qwsel2: uint32, shift_qws: uint2)
        | BN_MULH(wrd: reg256_t, wrs1: reg256_t, hw1: bool, wrs2: reg256_t, hw2: bool)
        | BN_SUB(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        | BN_SUBB(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        | BN_SUBI(wrd: reg256_t, wrs1: reg256_t, imm: uint256, fg: uint1)
        | BN_SUBM(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t)
        | BN_AND(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t)
        | BN_OR(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t)
        | BN_NOT(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t)
        | BN_XOR(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t)
        | BN_RSHI(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, imm: uint256)
        | BN_SEL(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, fg: uint1)
        | BN_CMP(wrs1: reg256_t, wrs2: reg256_t, fg: uint1)
        | BN_CMPB(wrs1: reg256_t, wrs2: reg256_t, fg: uint1)
        | BN_LID(grd: reg32_t, grd_inc: bool, offset: uint32, grs: reg32_t, grs_inc: bool)
        | BN_SID(grs2: reg32_t, grs2_inc: bool, offset: uint32, grs1: reg32_t, grs1_inc: bool)
        | BN_MOV(wrd: reg256_t, wrs: reg256_t)
        | BN_MOVR(grd: reg32_t, grd_inc: bool, grs: reg32_t, grs_inc: bool)
        | BN_WSRRS // TODO
        | BN_WSRRW // TODO

    datatype code =
        | Ins32(ins: ins32)
        | Ins256(bn_ins: ins256)
        | Block(block: codes)
        | While(whileCond: whileCond, whileBody: code)

    datatype codes = 
        | CNil
        | va_CCons(hd: code, tl: codes)

    datatype whileCond = 
        | RegCond(r: reg32_t)
        | ImmCond(c: uint32)

    // datatype flag = CF | MSB | LSB | ZERO
    datatype flags_t = flags_t(cf: bool, msb: bool, lsb: bool, zero: bool)

    datatype fgroups_t = fgroups_t(fg0: flags_t, fg1: flags_t)

    type gprs_t = gprs : seq<uint32> | |gprs| == 32 witness *

    type wdrs_t = wdrs : seq<uint256> | |wdrs| == 32 witness *

    predicate valid_wdr_view(wdrs: wdrs_t, slice: seq<uint256>, start: nat, len: nat)
    {   
        && |slice| == len
        && start + len <= 32
        && wdrs[start..start+len] == slice
    }

    datatype uint512_raw = uint512_cons(
        lh: uint256, uh: uint256, full: uint512)

	type uint512_view_t = num: uint512_raw |
		&& num.lh == uint512_lh(num.full)
		&& num.uh == uint512_uh(num.full)
		witness *

    predicate valid_uint512_view(
        wdrs: wdrs_t, num: uint512_view_t,
        li: int, ui: int)
        requires -1 <= li < BASE_5;
        requires -1 <= ui < BASE_5;
    {
        && (li > 0 ==> wdrs[li] == num.lh)
        && (ui > 0 ==> wdrs[ui] == num.uh)
    }

    /* start wmem_t realted */

    type wmem_t = map<int, seq<uint256>>

    predicate valid_buff_addr(wmem: wmem_t, base_addr: int, num_words: int)
    {
        // base_addr maps to some buffer in wmem
        && base_addr in wmem
        // the length is correct
        && num_words == |wmem[base_addr]|
        // the buffer is not empty
        && num_words != 0
        // the buffer doesn't expand beyond memory bound
        && base_addr + num_words * 32 <= DMEM_LIMIT
    }

    datatype iter_t = iter_cons(base_addr: int, index: nat, buff: seq<uint256>)

    function bn_lid_next_iter(iter: iter_t, inc: bool): iter_t
    {
        iter.(index := if inc then iter.index + 1 else iter.index)
    }

    predicate valid_iter(wmem: wmem_t, iter: iter_t)
    {
        var base_addr := iter.base_addr;
        // base_addr points to a valid buffer
        && valid_buff_addr(wmem, base_addr, |iter.buff|)
        // the view is consistent with wmem
        && wmem[base_addr] == iter.buff
        // the index is within bound (or at end)
        && iter.index <= |iter.buff|
    }

    predicate admissible_wmem_addr(wmem: wmem_t, addr:int, iter: iter_t)
    {
        && valid_iter(wmem, iter)
        && addr == iter.base_addr + 32 * iter.index
    }

    predicate valid_wmem_addr(wmem: wmem_t, addr:int, iter: iter_t)
    {
        && admissible_wmem_addr(wmem, addr, iter)
        // tighter constraint so we can dereference
        && iter.index < |iter.buff|
    }

    /* end wmem_t realted */

    predicate valid_xmem_addr(h: map<int, uint32>, addr:int)
    {
        addr in h
    }

    datatype state = state(
        gprs: gprs_t, // 32-bit registers
        wdrs: wdrs_t, // 256-bit registers

        wmod: uint256,
        wrnd: uint256,
        wacc: uint256,

        fgroups: fgroups_t,

        xmem: map<int, uint32>,
        wmem: wmem_t,

        ok: bool)

    predicate valid_state(s: state)
    {
        s.ok
    }
}
