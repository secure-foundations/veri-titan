include "vt_consts.dfy"
include "bv_ops.dfy"
include "vt_mem.dfy"

include "../libraries/src/NonlinearArithmetic/Power2.dfy"

module vt_ops {
    import opened Power2
    import NT = NativeTypes

    import opened bv_ops
    import opened vt_consts
    import opened vt_mem

/* registers definions */

    type reg_index = uint5

    datatype reg32_t = GPR(index: reg_index)

    type gprs_t = gprs : seq<uint32>
        | |gprs| == 32 witness *

    datatype reg256_t =
        | WDR(index: reg_index)
        | WMOD // Wide modulo register
        | WRND // Wide random number
        | WACC // Wide accumulator

    predicate is_wide_data_register(r: reg256_t)
    {
        r.WDR?
    }

    type wdrs_t = wdrs : seq<uint256>
        | |wdrs| == 32 witness *

/* wdr_view definion (SHADOW) */

    datatype uint512_raw = uint512_cons(
        lh: uint256, uh: uint256, full: uint512)

    type uint512_view_t = num: uint512_raw |
        && num.lh == uint512_lh(num.full)
        && num.uh == uint512_uh(num.full)
        witness *

    predicate valid_uint512_view(
        wdrs: wdrs_t, num: uint512_view_t,
        li: int, ui: int)
        requires -1 <= li < NT.BASE_5;
        requires -1 <= ui < NT.BASE_5;
    {
        && (li == NA || wdrs[li] == num.lh)
        && (ui == NA || wdrs[ui] == num.uh)
    }

    predicate valid_wdr_view(wdrs: wdrs_t, view: seq<uint256>, start: nat, len: nat)
    {   
        && |view| == len
        && start + len <= 32
        && wdrs[start..start+len] == view
    }

/* flags definions */

    // datatype flag = CF | MSB | LSB | ZERO
    datatype flags_t = flags_t(cf: bool, msb: bool, lsb: bool, zero: bool)

    datatype fgroups_t = fgroups_t(fg0: flags_t, fg1: flags_t)

    function method select_fgroup(fgps: fgroups_t, which: uint1): flags_t
    {
        if which == 0 then fgps.fg0 else fgps.fg1
    }

    function method get_flag(fgps: fgroups_t, which_group: uint1, which_flag: uint2) : bool
    {
        if which_flag == 0 then select_fgroup(fgps, which_group).cf 
        else if which_flag == 1 then select_fgroup(fgps, which_group).msb
        else if which_flag == 2 then select_fgroup(fgps, which_group).lsb
        else select_fgroup(fgps, which_group).zero
    }

    function method update_fgroups(fgps: fgroups_t, which_group: uint1, new_flags: flags_t) : fgroups_t
    {
        if which_group == 0 then fgps.(fg0 := new_flags) else fgps.(fg1 := new_flags)
    }

/* instruction definions */

    datatype ins32 =
        | ADD(xrd: reg32_t, xrs1: reg32_t, xrs2: reg32_t)
        | ADDI(xrd: reg32_t, xrs1: reg32_t, imm: int12)
        | LW(xrd: reg32_t, xrs1: reg32_t, offset: int12)
        | SW(xrs1: reg32_t, xrs2: reg32_t, offset: int12)
        // | LOOP(grs: reg32_t, bodysize: uint32)
        // | LOOPI(iterations: uint32, bodysize: uint32)
        | LI(xrd: reg32_t, imm32: uint32)

    datatype ins256 =
        | BN_ADD(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        | BN_ADDC(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        | BN_ADDI(wrd: reg256_t, wrs1: reg256_t, imm: uint10, fg: uint1)
        // | BN_ADDM(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t)
        | BN_MULQACC(zero: bool, wrs1: reg256_t, qwsel1: uint2, wrs2: reg256_t, qwsel2: uint2, shift_qws: uint2)
        | BN_MULQACC_SO(zero: bool, wrd: reg256_t, lower: bool, wrs1: reg256_t, qwsel1: uint2, wrs2: reg256_t, qwsel2: uint2, shift_qws: uint2)
        | BN_SUB(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        | BN_SUBB(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        // | BN_SUBI(wrd: reg256_t, wrs1: reg256_t, imm: uint10, fg: uint1)
        // | BN_SUBM(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t)
        // | BN_AND(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        // | BN_OR(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        // | BN_NOT(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        | BN_XOR(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        // | BN_RSHI(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, imm: uint256)
        | BN_SEL(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, fg: uint1, flag: uint2)
        // | BN_CMP(wrs1: reg256_t, wrs2: reg256_t, fg: uint1)
        // | BN_CMPB(wrs1: reg256_t, wrs2: reg256_t, fg: uint1)
        | BN_LID(grd: reg32_t, grd_inc: bool, offset: int10, grs: reg32_t, grs_inc: bool)
        | BN_SID(grs2: reg32_t, grs2_inc: bool, offset: int10, grs1: reg32_t, grs1_inc: bool)
        | BN_MOV(wrd: reg256_t, wrs: reg256_t)
        | BN_MOVR(grd: reg32_t, grd_inc: bool, grs: reg32_t, grs_inc: bool)
        // | BN_WSRRS 
        // | BN_WSRRW

/* stateless semantic functions  */

    function mod_add(a: nat, b: nat, m: nat): nat 
        requires a < m && b < m;
    {
        if a + b > m then a + b - m else a + b
    }

    function method set_flags(carry: uint1, value: uint256): flags_t
    {
        flags_t(carry == 1, uint256_msb(value) == 1, uint256_lsb(value) == 1, value == 0)
    }

    function method otbn_addc(x: uint256, y: uint256, shift: shift_t, carry: bool) : (uint256, flags_t)
    {
        var cin := if carry then 1 else 0;
        var (sum, cout) := uint256_addc(x, uint256_sb(y, shift), cin);
        (sum, set_flags(cout, sum))
    }

    function method otbn_subb(x: uint256, y: uint256, shift: shift_t, borrow: bool) : (uint256, flags_t)
    {
        var cf := if borrow then 1 else 0;
        var (diff, cout) := uint256_subb(x, uint256_sb(y, shift), cf);
        (diff, set_flags(cout, diff))
    }

    function method otbn_mulqacc(
        zero: bool,
        x: uint256, qx: uint2,
        y: uint256, qy: uint2,
        shift: uint2,
        acc: uint256) : uint256
    {
        var product := uint256_qmul(x, qx, y, qy);
        var shift := uint256_sb(product, SFT(true, shift * 8));
        if zero then shift else (acc + shift) % NT.BASE_256
    }

    predicate otbn_mulqacc_is_safe(shift: uint2, acc: uint256)
    {
        // make sure no overflow from shift (product needs to be 128 bits)
        && (shift <= 2) 
        // make sure no overflow from addtion
        && (acc + otbn_qshift_safe(NT.BASE_128 - 1, shift) < NT.BASE_256)
    }

    // quater shift but no overflow
    function otbn_qshift_safe(x: uint256, q: uint2): (r: uint256)
        requires (q == 1) ==> (x < BASE_192);
        requires (q == 2) ==> (x < NT.BASE_128);
        requires (q == 3) ==> (x < NT.BASE_64);
    {
        if q == 0 then x
        else if q == 1 then x * NT.BASE_64
        else if q == 2 then x * NT.BASE_128
        else x * BASE_192
    }


    // mulquacc but no overflow
    function otbn_mulqacc_safe(
        zero: bool,
        x: uint256, qx: uint2,
        y: uint256, qy: uint2,
        shift: uint2,
        acc: uint256) : uint256

        requires otbn_mulqacc_is_safe(shift, acc);
    {
        var product := uint256_qmul(x, qx, y, qy);
        var shift := otbn_qshift_safe(product, shift);
        if zero then shift else acc + shift
    }

    lemma otbn_mulqacc_safe_correct(
        zero: bool,
        x: uint256, qx: uint2,
        y: uint256, qy: uint2,
        shift: uint2,
        acc: uint256)
        requires otbn_mulqacc_is_safe(shift, acc);
        ensures otbn_mulqacc_safe(zero, x, qx, y, qy, shift, acc)
            == otbn_mulqacc(zero, x, qx, y, qy, shift, acc);
    {
    }

    function method otbn_xor(x: uint256, y: uint256, shift: shift_t, carry: bool): (uint256, flags_t)
    {
        var result := uint256_xor(x, uint256_sb(y, shift));
        // keep the old carry
        (result, set_flags(bool_to_uint1(carry), result))
    }

    function method otbn_sel(x: uint256, y: uint256, sel: bool): uint256
    {
        if sel then x else y
    }

    // function otbn_rshi(x: uint256, y: uint256, shift_amt: int) : uint256
    //     requires 0 <= shift_amt < 256;
    // {
    //     var concat : int := x * NT.BASE_256 + y;
    //     (concat / Pow2(shift_amt)) % NT.BASE_256
    // }

/* control flow definions */

    datatype code =
        | Ins32(ins: ins32)
        | Ins256(bn_ins: ins256)
        | Block(block: codes)
        | While(whileCond: whileCond, whileBody: code)
        | Comment(com: string)

    datatype codes = 
        | CNil
        | va_CCons(hd: code, tl: codes)

    datatype whileCond = 
        | RegCond(r: reg32_t)
        | ImmCond(c: uint32)

/* state definions */

    datatype state = state(
        gprs: gprs_t, // 32-bit registers
        wdrs: wdrs_t, // 256-bit registers

        wmod: uint256,
        wrnd: uint256,
        wacc: uint256,

        fgroups: fgroups_t,

        xmem: xmem_t,
        wmem: wmem_t,

        ok: bool)
    {
        static function method init(): state
        {
            var flags := flags_t(false, false, false, false);
            state(seq(32, n => 0), seq(32, n => 0), 0, 0, 0,
                fgroups_t(flags, flags),
                map[], map[], true)
        }

        function method read_reg32(r: reg32_t): uint32
        {
            if r.index == 0 then 0
            else gprs[r.index]
        }

        function method write_reg32(r: reg32_t, v: uint32): state
        {
            if r.index == 0 then this
            else this.(gprs := gprs[r.index := v])
        }

        function method read_xmem(addr: uint32): uint32
            requires xmem_addr_admissible(addr)
        {
            if addr in xmem then xmem[addr] else 0
        }

        function method write_xmem(addr: uint32, v: uint32): state
            requires xmem_addr_admissible(addr)
        {
            this.(xmem := xmem[addr := v])
        }

        function method eval_ADD(xrd: reg32_t, xrs1: reg32_t, xrs2: reg32_t): state
        {
            var v1 := read_reg32(xrs1);
            var v2 := read_reg32(xrs2);
            var sum := uint32_add(v1, v2);
            write_reg32(xrd, sum)
        }

        function method eval_ADDI(xrd: reg32_t, xrs1: reg32_t, imm: int12): state
        {
            var v1 := read_reg32(xrs1);
            var sum := uint32_addi(v1, imm);
            write_reg32(xrd, sum)
        }

        function method eval_LW(xrd: reg32_t, xrs1: reg32_t, offset: int12): state
        {
            var base := read_reg32(xrs1);
            var addr := uint32_addi(base, offset);
            if !xmem_addr_admissible(addr) then this.(ok := false)
            else write_reg32(xrd, read_xmem(addr))
        }

        function method eval_SW(xrs1: reg32_t, xrs2: reg32_t, offset: int12): state
        {
            var base := read_reg32(xrs1);
            var addr := uint32_addi(base, offset);
            if !xmem_addr_admissible(addr) then this.(ok := false)
            else write_xmem(addr, read_reg32(xrs2))
        }

        function method eval_LI(xrd: reg32_t, imm: uint32): state
        {
            write_reg32(xrd, imm)
        }

        function method read_reg256(r: reg256_t) : uint256
        {
            match r {
                case WDR(index) => wdrs[r.index]
                case WMOD => wmod
                case WRND => wrnd
                case WACC => wacc
            }
        }

        function method write_reg256(r: reg256_t, v: uint256): state
        {
            match r {
                case WDR(index) => this.(wdrs := wdrs[r.index := v])
                case WMOD => this.(wmod := v)
                case WRND => this.(wrnd := v)
                case WACC => this.(wacc := v)
            }
        }

        function method read_flag(which_group: uint1, which_flag: uint2): bool
        {
            get_flag(fgroups, which_group, which_flag)
        }

        function method write_flags(which_group: uint1, new_flags: flags_t): state
        {
            this.(fgroups := update_fgroups(fgroups, which_group, new_flags))
        }

        function method read_wmem(addr: uint32): uint256 
            requires wmem_addr_admissible(addr)
        {
            if addr in wmem then wmem[addr] else 0
        }

        function method write_wmem(addr: uint32, v: uint256): state 
            requires wmem_addr_admissible(addr)
        {
            this.(wmem := wmem[addr := v])
        }

        function method eval_BN_LID(grd: reg32_t, grd_inc: bool, offset: int10, grs: reg32_t, grs_inc: bool): state
            // grd and grs should not be the same
        {
            var di := read_reg32(grd);
            var base := read_reg32(grs);
            var addr := wmem_offsetted_addr(base, offset);
            if di > 31 || !wmem_addr_admissible(addr) then 
                this.(ok := false)
            else
                var value := read_wmem(addr);
                // write to wdr[grd]
                write_reg256(WDR(di), value).
                // update grd
                write_reg32(grd, if grd_inc then di + 1 else di).
                // update grs
                write_reg32(grs, if grs_inc then uint32_add(base, 32) else base)
        }

        function method eval_BN_SID(grs2: reg32_t, grs2_inc: bool, offset: int10, grs1: reg32_t, grs1_inc: bool): state
        {
            var di := read_reg32(grs2);
            var base := read_reg32(grs1);
            var addr := wmem_offsetted_addr(base, offset);
            if di > 31 || !wmem_addr_admissible(addr) then 
                this.(ok := false)
            else
                var value := read_reg256(WDR(di));
                write_wmem(addr, value).
                write_reg32(grs1, if grs1_inc then uint32_add(base, 32) else base).
                write_reg32(grs2, if grs2_inc then di + 1 else di)
        }

        function method eval_BN_ADD(wrd: reg256_t, wrs1: reg256_t, wrs2: 
        reg256_t, shift: shift_t, fg: uint1): state
        {
            var v1 := read_reg256(wrs1);
            var v2 := read_reg256(wrs2);
            var (sum, flags) := otbn_addc(v1, v2, shift, false);
            write_reg256(wrd, sum).write_flags(fg, flags)
        }

        function method eval_BN_ADDC(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1): state
        {
            var v1 := read_reg256(wrs1);
            var v2 := read_reg256(wrs2);
            var carry := read_flag(fg, 0);
            var (sum, flags) := otbn_addc(v1, v2, shift, carry);
            write_reg256(wrd, sum).write_flags(fg, flags)
        }

        function method eval_BN_ADDI(wrd: reg256_t, wrs1: reg256_t, imm: uint10, fg: uint1): state
        {
            var v1 := read_reg256(wrs1);
            var (sum, flags) := otbn_addc(v1, imm, SFT_DFT, false);
            write_reg256(wrd, sum).write_flags(fg, flags)
        }

        function method eval_BN_MULQACC(zero: bool,
            wrs1: reg256_t, qwsel1: uint2,
            wrs2: reg256_t, qwsel2: uint2,
            shift_qws: uint2): state
        {
            var v1 := read_reg256(wrs1);
            var v2 := read_reg256(wrs2);
            var v3 := read_reg256(WACC);
            var product := otbn_mulqacc(zero, v1, qwsel1, v2, qwsel2, shift_qws, v3);
            write_reg256(WACC, product)
        }
        
        function method eval_BN_MULQACC_SO(zero: bool,
            wrd: reg256_t, lower: bool,
            wrs1: reg256_t, qwsel1: uint2,
            wrs2: reg256_t, qwsel2: uint2,
            shift_qws: uint2): state
        {
            var v1 := read_reg256(wrs1);
            var v2 := read_reg256(wrs2);
            var v3 := read_reg256(WACC);
            var v4 := read_reg256(wrd);
            var product := otbn_mulqacc(zero, v1, qwsel1, v2, qwsel2, shift_qws, v3);
            var lh, uh := uint256_lh(product), uint256_uh(product);
            // the upper half stay in wacc
            write_reg256(WACC, uh).
            // the lower half gets written back into dst
            write_reg256(wrd, uint256_hwb(v4, lh, lower))
        }

        function method eval_BN_SUB(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1): state
        {
            var v1 := read_reg256(wrs1);
            var v2 := read_reg256(wrs2);
            var (diff, flags) := otbn_subb(v1, v2, shift, false);
            write_reg256(wrd, diff).write_flags(fg, flags)
        }
        
        function method eval_BN_SUBB(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1): state
        {
            var v1 := read_reg256(wrs1);
            var v2 := read_reg256(wrs2);
            var borrow := read_flag(fg, 0);
            var (diff, flags) := otbn_subb(v1, v2, shift, borrow);
            write_reg256(wrd, diff).write_flags(fg, flags)
        }

        function method eval_BN_XOR(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1): state
        {
            var v1 := read_reg256(wrs1);
            var v2 := read_reg256(wrs2);
            var carry := read_flag(fg, 0);
            var (result, flags) := otbn_xor(v1, v2, shift, carry);
            write_reg256(wrd, result).write_flags(fg, flags)
        }

        function method eval_BN_SEL(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, fg: uint1, flag: uint2): state
        {
            var v1 := read_reg256(wrs1);
            var v2 := read_reg256(wrs2);
            var sel := read_flag(fg, flag);
            var result := otbn_sel(v1, v2, sel);
            write_reg256(wrd, result)
        }

        function method eval_BN_MOV(wrd: reg256_t, wrs: reg256_t): state
        {
            write_reg256(wrd, read_reg256(wrs))
        }

        function method eval_BN_MOVR(grd: reg32_t, grd_inc: bool, grs: reg32_t, grs_inc: bool): state
        {
            var di := read_reg32(grd);
            var si := read_reg32(grs);
            if di > 31 || si > 31 then 
                this.(ok := false)
            else
                write_reg32(grd, if grd_inc then di + 1 else di).
                write_reg32(grs, if grs_inc then si + 1 else si).
                write_reg256(WDR(di), read_reg256(WDR(si)))
        }

        function method eval_ins32(xins: ins32): state
        {
            if !ok then
                this
            else match xins
                case ADD(xrd, xrs1, xrs2) => eval_ADD(xrd, xrs1, xrs2)
                case ADDI(xrd, xrs1, imm) => eval_ADDI(xrd, xrs1, imm)
                case LW(xrd, xrs1, offset) => eval_LW(xrd, xrs1, offset)
                case SW(xrs2, xrs1, offset) => eval_SW(xrs1, xrs2, offset)
                case LI(xrd, imm32) => eval_LI(xrd, imm32)
        }

        function method eval_ins256(wins: ins256): state
        {
            if !ok then
                this
            else match wins
                case BN_ADD(wrd, wrs1, wrs2, shift, fg) =>
                    eval_BN_ADD(wrd, wrs1, wrs2, shift, fg)
                case BN_ADDC(wrd, wrs1, wrs2, shift, fg) =>
                    eval_BN_ADDC(wrd, wrs1, wrs2, shift, fg)
                case BN_ADDI(wrd, wrs1, imm, fg) =>
                    eval_BN_ADDI(wrd, wrs1, imm, fg)
                case BN_MULQACC(zero, wrs1, qwsel1, wrs2, qwsel2, shift_qws) =>
                    eval_BN_MULQACC(zero, wrs1, qwsel1, wrs2, qwsel2, shift_qws)
                case BN_MULQACC_SO(zero, wrd, lower, wrs1, qwsel1, wrs2, qwsel2, shift_qws) =>
                    eval_BN_MULQACC_SO(zero, wrd, lower, wrs1, qwsel1, wrs2, qwsel2, shift_qws)
                case BN_SUB(wrd, wrs1, wrs2, shift, fg) => 
                    eval_BN_SUB(wrd, wrs1, wrs2, shift, fg)
                case BN_SUBB(wrd, wrs1, wrs2, shift, fg) => 
                    eval_BN_SUBB(wrd, wrs1, wrs2, shift, fg)
                case BN_XOR(wrd, wrs1, wrs2, shift, fg) => 
                    eval_BN_XOR(wrd, wrs1, wrs2, shift, fg)
                case BN_SEL(wrd, wrs1, wrs2, fg, flag) => 
                    eval_BN_SEL(wrd, wrs1, wrs2, fg, flag)
                case BN_MOV(wrd, wrs) =>
                    eval_BN_MOV(wrd, wrs)
                case BN_MOVR(grd, grd_inc, grs, grs_inc) =>
                    eval_BN_MOVR(grd, grd_inc, grs, grs_inc)
                case BN_LID(grd, grd_inc, offset, grs, grs_inc) =>
                    eval_BN_LID(grd, grd_inc, offset, grs, grs_inc)
                case BN_SID(grs2, grs2_inc, offset, grs1, grs1_inc) =>
                    eval_BN_SID(grs2, grs2_inc, offset, grs1, grs1_inc)
        }

        function method eval_block(block: codes): state
            decreases block
        {
            if block.CNil? then
                this
            else
                eval_code(block.hd).eval_block(block.tl)
        }

        function method eval_cond(wc: whileCond): nat
        {
            match wc 
                case RegCond(r) => read_reg32(r)
                case ImmCond(c) => c
        }

        function method eval_while(c: code, n: nat): state
            decreases c, n
        {
            if !ok then
                this
            else
                if n == 0 then
                    this
                else
                    eval_code(c).eval_while(c, n - 1)
        }

        function method eval_code(c: code): state
            decreases c, 0
        {
            match c
                case Ins32(ins) => eval_ins32(ins)
                case Ins256(ins) => eval_ins256(ins)
                case Block(block) => eval_block(block)
                case While(cond, body) => eval_while(body, eval_cond(cond))
                case Comment(com) => this
        }

        method dump_regs()
        {
            var i := 0;
            while i < 32
            {
                print("x"); print(i); print("\t");
                print(read_reg32(GPR(i))); print("\n"); 
                i := i + 1;
            }

            i := 0;
            while i < 32
            {
                print("w"); print(i); print("\t");
                print(read_reg256(WDR(i))); print("\n"); 
                i := i + 1;
            }
        }

        method dump_wmem(addr: uint32, words: uint32)
            requires wmem_addr_admissible(addr + words * 32)
        {
            var end := addr + words * 32;
            var i := 0;
            var cur := addr;

            while cur < end
                invariant cur == addr + i * 32
                invariant wmem_addr_admissible(cur)
                decreases end - cur
            {
                var value := read_wmem(cur);
                print(cur); print(":"); print(value); print("\n");
                i := i + 1;
                cur := cur + 32;
            }
        }
    }

    predicate valid_state(s: state)
    {
        && s.ok
    }
}
