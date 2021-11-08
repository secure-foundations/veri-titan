include "../../lib/bv32_ops.dfy"
include "../../lib/bv256_ops.dfy"

module ot_machine {
    import Mul

    import bv32_ops
    import bv256_ops
    import opened integers

    const DMEM_LIMIT: int := 0x8000
    const NUM_WORDS:  int := 12

    // ignore the mapping
    const NA :int := -1;

/* registers definitions */

    type reg_index = uint5

    datatype reg32_t = GPR(index: reg_index)

    type gprs_t = gprs : seq<uint32>
        | |gprs| == 32 witness *

    datatype reg256_t =
        | WDR(index: reg_index)
        | WMOD // Wide modulo register
        | WRND // Wide random number
        | WURND // Wide urandom number
        | WACC // Wide accumulator

    predicate is_wide_data_register(r: reg256_t)
    {
        r.WDR?
    }

    type wdrs_t = wdrs : seq<uint256>
        | |wdrs| == 32 witness *


/* flags definitions */

    // datatype flag = CF | MSB | LSB | ZERO
    datatype flags_t = flags_t(cf: bool, msb: bool, lsb: bool, zero: bool)
    {
        function method to_nat(): nat
        {
            var r := if cf then 1 else 0;
            var r := r + if msb then 2 else 0;
            var r := r + if lsb then 4 else 0;
            r + if zero then 8 else 0
        }

        function method get_single_flag(which_flag: uint2): bool
        {
            if which_flag == 0 then cf 
            else if which_flag == 1 then msb
            else if which_flag == 2 then lsb
            else zero
        }
    }

    datatype fgroups_t = fgroups_t(fg0: flags_t, fg1: flags_t)

    function method get_fgroup(fgps: fgroups_t, which: uint1): flags_t
    {
        if which == 0 then fgps.fg0 else fgps.fg1
    }

    function method get_flag(fgps: fgroups_t, which_group: uint1, which_flag: uint2) : bool
    {
        get_fgroup(fgps, which_group).get_single_flag(which_flag)
    }

    function method update_fgroups(fgps: fgroups_t, which_group: uint1, new_flags: flags_t): fgroups_t
    {
        if which_group == 0 then fgps.(fg0 := new_flags) else fgps.(fg1 := new_flags)
    }

/* shift definitions */

    datatype shift_t = SFT(left: bool, bytes: uint5)

    const SFT_DFT :shift_t := SFT(true, 0);

/* instruction definitions */

    datatype ins32 =
        | ADD(xrd: reg32_t, xrs1: reg32_t, xrs2: reg32_t)
        | ADDI(xrd: reg32_t, xrs1: reg32_t, imm: int12)
        | LW(xrd: reg32_t, offset: int12, xrs1: reg32_t)
        | SW(xrs2: reg32_t, offset: int12, xrs1: reg32_t)
        // | LOOP(grs: reg32_t, bodysize: uint32)
        // | LOOPI(iterations: uint32, bodysize: uint32)
        | LI(xrd: reg32_t, imm32: uint32)
        | ECALL

    datatype ins256 =
        | BN_ADD(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        | BN_ADDC(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        | BN_ADDI(wrd: reg256_t, wrs1: reg256_t, imm: uint10, fg: uint1)
        // | BN_ADDM(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t)
        | BN_MULQACC(zero: bool, wrs1: reg256_t, qwsel1: uint2, wrs2: reg256_t, qwsel2: uint2, shift_qws: uint2)
        | BN_MULQACC_SO(zero: bool, wrd: reg256_t, lower: bool,
            wrs1: reg256_t, qwsel1: uint2, wrs2: reg256_t, qwsel2: uint2,
            shift_qws: uint2, fg: uint1)
        | BN_SUB(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        | BN_SUBB(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        // | BN_SUBI(wrd: reg256_t, wrs1: reg256_t, imm: uint10, fg: uint1)
        // | BN_SUBM(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t)
        // | BN_AND(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        // | BN_OR(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        | BN_NOT(wrd: reg256_t, wrs: reg256_t, shift: shift_t, fg: uint1)
        | BN_XOR(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift: shift_t, fg: uint1)
        // | BN_RSHI(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, imm: uint256)
        | BN_SEL(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, fg: uint1, flag: uint2)
        // | BN_CMP(wrs1: reg256_t, wrs2: reg256_t, fg: uint1)
        // | BN_CMPB(wrs1: reg256_t, wrs2: reg256_t, fg: uint1)
        | BN_LID(grd: reg32_t, grd_inc: bool, offset: int10, grs: reg32_t, grs_inc: bool)
        | BN_SID(grs2: reg32_t, grs2_inc: bool, offset: int10, grs1: reg32_t, grs1_inc: bool)
        | BN_MOV(wrd: reg256_t, wrs: reg256_t)
        | BN_MOVR(grd: reg32_t, grd_inc: bool, grs: reg32_t, grs_inc: bool)
        | BN_WSRR(wrd: reg256_t, wsr: uint2)
        // | BN_WSRRW

/* stateless semantic functions  */

    function method set_mlz_flags(carry: uint1, value: uint256): flags_t
    {
        flags_t(carry == 1, bv256_ops.msb(value) == 1, bv256_ops.lsb(value) == 1, value == 0)
    }

    function method otbn_shift(b: uint256, shift: shift_t) : uint256
    {
        var num_bits := (shift.bytes as int) * 8;
        if num_bits == 0 then b
        else if shift.left then bv256_ops.ls(b, num_bits)
        else bv256_ops.rs(b, num_bits)
    }

    function method otbn_addc(x: uint256, y: uint256, shift: shift_t, carry: bool) : (uint256, flags_t)
    {
        var cin := if carry then 1 else 0;
        var (sum, cout) := bv256_ops.addc(x, otbn_shift(y, shift), cin);
        (sum, set_mlz_flags(cout, sum))
    }

    function method otbn_subb(x: uint256, y: uint256, shift: shift_t, borrow: bool) : (uint256, flags_t)
    {
        var cf := if borrow then 1 else 0;
        var (diff, cout) := bv256_ops.subb(x, otbn_shift(y, shift), cf);
        (diff, set_mlz_flags(cout, diff))
    }

    function method {:opaque} otbn_qsel(x: uint256, qx: uint2): uint64
    {
        if qx == 0 then
            bv256_ops.lh(x) % BASE_64
        else if qx == 1 then
            bv256_ops.lh(x) / BASE_64
        else if qx == 2 then
            bv256_ops.uh(x) % BASE_64
        else
            bv256_ops.uh(x) / BASE_64
    }

    function method {:opaque} otbn_qmul(x: uint256, qx: uint2, y: uint256, qy: uint2): uint128
    {
        var src1 := otbn_qsel(x, qx);
        var src2 := otbn_qsel(y, qy);
        assume src1 as nat * src2 as nat < BASE_128;
        Mul.LemmaMulStrictlyIncreasesAuto();
        src1 as uint128 * src2 as uint128
    }

    function method otbn_mulqacc(
        zero: bool,
        x: uint256, qx: uint2,
        y: uint256, qy: uint2,
        shift: uint2,
        acc: uint256) : uint256
    {
        var product := otbn_qmul(x, qx, y, qy);
        var shift := otbn_shift(product, SFT(true, shift * 8));
        if zero then shift else bv256_ops.add(acc, shift)
    }

    datatype mulqacc_so_result_t = mulqacc_so_result_t(
        new_acc: uint256,
        new_dst: uint256,
        new_flags: flags_t)

    function method {:opaque} otbn_hwb(x: uint256, v: uint128, lower: bool): (x': uint256)
        // overwrites the lower half, keeps the higher half
        ensures lower ==> (bv256_ops.lh(x') == v && bv256_ops.uh(x') == bv256_ops.uh(x));
        // overwrites the higher half, keeps the lower half
        ensures !lower ==> (bv256_ops.uh(x') == v && bv256_ops.lh(x') == bv256_ops.lh(x));
    {
        var uh, lh := bv256_ops.uh(x), bv256_ops.lh(x);
        reveal bv256_ops.lh();
        reveal bv256_ops.uh();
        if lower then v + uh * BASE_128
        else lh + v * BASE_128
    }

    // lemma hwb_lemma(x1: uint256, x2: uint256, x3: uint256, lo: uint128, hi: uint128)
    //     requires x2 == hwb(x1, lo, true);
    //     requires x3 == hwb(x2, hi, false);
    //     ensures x3 == lo + hi * BASE_128;
    // {
    //     calc == {
    //         x3;
    //             { half_split_lemma(x3); }
    //         lh(x3) + uh(x3) * BASE_128;
    //             { assert uh(x3) == hi && lh(x3) == lh(x2); }
    //         lh(x2) + hi * BASE_128;
    //             { assert lh(x2) == lo; }
    //         lo + hi * BASE_128;
    //     }
    // }

/* start: I don't want to write other bv modules just for two operations */

    function method {:opaque} uint128_msb(x: uint128): uint1
    {
        if ((x as bv128 >> 127) & 1 == 1) then 1 else 0
    }

    function method {:opaque} uint128_lsb(x: uint128): uint1
    {
        x % 2
    }

    function method {:opaque} uint512_lh(x: uint512): uint256
    {
        x % BASE_256
    }

    function method {:opaque} uint512_uh(x: uint512): uint256
    {
        x / BASE_256
    }

/* end: I don't want to write other bv modules just for two operations */

    function method otbn_mulqacc_so(product: uint256, z: uint256, lower: bool, flags: flags_t) : mulqacc_so_result_t
    {
        var lh, uh := bv256_ops.lh(product), bv256_ops.uh(product);
        var new_flags :=
            (if lower then
                flags_t(flags.cf, flags.msb, uint128_lsb(lh) == 1, lh == 0)
            else
                flags_t(flags.cf, uint128_msb(lh) == 1, flags.lsb, (lh == 0) && flags.zero));
        mulqacc_so_result_t(uh, otbn_hwb(z, lh, lower), new_flags)
    }

    function method otbn_not(x: uint256, shift: shift_t, carry: bool): (uint256, flags_t)
    {
        var result := bv256_ops.not(otbn_shift(x, shift));
        // keep the old carry
        (result, set_mlz_flags(bv256_ops.bool_to_uint1(carry), result))
    }

    function method otbn_xor(x: uint256, y: uint256, shift: shift_t, carry: bool): (uint256, flags_t)
    {
        var result := bv256_ops.xor(x, otbn_shift(y, shift));
        // keep the old carry
        (result, set_mlz_flags(bv256_ops.bool_to_uint1(carry), result))
    }

    function method otbn_sel(x: uint256, y: uint256, sel: bool): uint256
    {
        if sel then x else y
    }

    function method wwrod_offset_ptr(base: uint32, offset: int10): uint32
    {
        bv32_ops.addi(base, offset * 32)
    }

/* mem_t definion */

    // admissible is aligned and bounded
    predicate method xword_ptr_admissible(ptr: nat)
    {
        && ptr % 4 == 0
        && ptr < DMEM_LIMIT
    }

    // admissible is aligned and bounded
    predicate method wword_ptr_admissible(ptr: nat)
    {
        && ptr % 32 == 0
        && ptr < DMEM_LIMIT
    }

    type mem_t = map<int, uint32>

    predicate method wword_ptr_valid(mem: mem_t, ptr: nat)
    {
        && wword_ptr_admissible(ptr)
        && ptr + 0 in mem
        && ptr + 4 in mem
        && ptr + 8 in mem
        && ptr + 12 in mem
        && ptr + 16 in mem
        && ptr + 20 in mem
        && ptr + 24 in mem
        && ptr + 28 in mem
    }

    function method read_wword(mem: mem_t, ptr: nat): uint256
        requires wword_ptr_valid(mem, ptr)
    {
        var p0 := mem[ptr + 0];
        var p1 := mem[ptr + 4];
        var p2 := mem[ptr + 8];
        var p3 := mem[ptr + 12];
        var p4 := mem[ptr + 16];
        var p5 := mem[ptr + 20];
        var p6 := mem[ptr + 24];
        var p7 := mem[ptr + 28];
        bv256_ops.eighth_assemble(p0, p1, p2, p3, p4, p5, p6, p7)
    }

    function method mem_write_wword(mem: mem_t, ptr: nat, value: uint256): (mem' : mem_t)
        requires wword_ptr_admissible(ptr)
        ensures wword_ptr_valid(mem', ptr)
    {
        mem[ptr + 0 := bv256_ops.eighth_split(value, 0)]
            [ptr + 4 := bv256_ops.eighth_split(value, 1)]
            [ptr + 8 := bv256_ops.eighth_split(value, 2)]
            [ptr + 12 := bv256_ops.eighth_split(value, 3)]
            [ptr + 16 := bv256_ops.eighth_split(value, 4)]
            [ptr + 20 := bv256_ops.eighth_split(value, 5)]
            [ptr + 24 := bv256_ops.eighth_split(value, 6)]
            [ptr + 28 := bv256_ops.eighth_split(value, 7)]
    }

/* control flow definitions */

    datatype code =
        | Ins32(ins: ins32)
        | Ins256(bn_ins: ins256)
        | Block(block: codes)
        | While(whileCond: whileCond, whileBody: code)
        | Function(name: string, functionBody: codes)
        | Comment(com: string)

    datatype codes = 
        | CNil
        | va_CCons(hd: code, tl: codes)

    datatype whileCond = 
        | RegCond(r: reg32_t)
        | ImmCond(c: uint32)

/* state definitions */

    datatype state = state(
        gprs: gprs_t, // 32-bit registers
        wdrs: wdrs_t, // 256-bit registers

        wmod: uint256,
        wrnd: uint256,
        wurnd: uint256,
        wacc: uint256,

        fgroups: fgroups_t,

        mem: mem_t,

        ok: bool)
    {
        static function method init(): state
        {
            var flags := flags_t(false, false, false, false);
                state(seq(32, n => 0), seq(32, n => 0),
                0, 0, 0, 0,
                fgroups_t(flags, flags),
                map[], true)
        }

        function method read_reg32(r: reg32_t): uint32
        {
            if r.index == 0 then 0
            else gprs[r.index]
        }

        function method write_reg32(r: reg32_t, v: uint32): state
        {
            if r.index == 0 || r.index == 1 then this
            else this.(gprs := gprs[r.index := v])
        }

        function method read_xword(addr: uint32): uint32
            requires xword_ptr_admissible(addr)
        {
            if addr in mem then mem[addr] else 0
        }

        function method write_xword(addr: uint32, v: uint32): state
            requires xword_ptr_admissible(addr)
        {
            this.(mem := mem[addr := v])
        }

        function method read_wword(addr: uint32): uint256 
            requires wword_ptr_admissible(addr)
        {
            var p0 := read_xword(addr + 0);
            var p1 := read_xword(addr + 4);
            var p2 := read_xword(addr + 8);
            var p3 := read_xword(addr + 12);
            var p4 := read_xword(addr + 16);
            var p5 := read_xword(addr + 20);
            var p6 := read_xword(addr + 24);
            var p7 := read_xword(addr + 28);
            bv256_ops.eighth_assemble(p0, p1, p2, p3, p4, p5, p6, p7)
        }

        function method write_wword(addr: uint32, v: uint256): state
            requires wword_ptr_admissible(addr)
        {
            var mem' := mem_write_wword(mem, addr, v);
            this.(mem := mem')
        }

        function method eval_ADD(xrd: reg32_t, xrs1: reg32_t, xrs2: reg32_t): state
        {
            var v1 := read_reg32(xrs1);
            var v2 := read_reg32(xrs2);
            var sum := bv32_ops.add(v1, v2);
            write_reg32(xrd, sum)
        }

        function method eval_ADDI(xrd: reg32_t, xrs1: reg32_t, imm: int12): state
        {
            var v1 := read_reg32(xrs1);
            var sum := bv32_ops.addi(v1, imm);
            write_reg32(xrd, sum)
        }

        function method eval_LW(xrd: reg32_t, offset: int12, xrs1: reg32_t): state
        {
            var base := read_reg32(xrs1);
            var addr := bv32_ops.addi(base, offset);
            if !xword_ptr_admissible(addr) then this.(ok := false)
            else write_reg32(xrd, read_xword(addr))
        }

        function method eval_SW(xrs2: reg32_t, offset: int12, xrs1: reg32_t): state
        {
            var base := read_reg32(xrs1);
            var addr := bv32_ops.addi(base, offset);
            if !xword_ptr_admissible(addr) then this.(ok := false)
            else write_xword(addr, read_reg32(xrs2))
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
                case WRND => 0x99999999_99999999_99999999_99999999_99999999_99999999_99999999_99999999
                case WURND => wurnd
                case WACC => wacc
            }
        }

        function method write_reg256(r: reg256_t, v: uint256): state
        {
            match r {
                case WDR(index) => this.(wdrs := wdrs[r.index := v])
                case WMOD => this.(wmod := v)
                case WURND => this
                case WRND => this
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

        function method eval_BN_LID(grd: reg32_t, grd_inc: bool, offset: int10, grs: reg32_t, grs_inc: bool): state
            // grd and grs should probably not be the same
        {
            var di := read_reg32(grd);
            var base := read_reg32(grs);
            var addr := wwrod_offset_ptr(base, offset);
            if di > 31 || !wword_ptr_admissible(addr) then 
                this.(ok := false)
            else
                var value := read_wword(addr);
                // update grd
                var s := (if grd_inc then write_reg32(grd, di + 1) else this);
                // update grs
                var l := (if grs_inc then s.write_reg32(grs, bv32_ops.add(base, 32)) else s);
                l.write_reg256(WDR(di), value)
        }

        function method eval_BN_SID(grs2: reg32_t, grs2_inc: bool, offset: int10, grs1: reg32_t, grs1_inc: bool): state
        {
            var di := read_reg32(grs2);
            var base := read_reg32(grs1);
            var addr := wwrod_offset_ptr(base, offset);
            if di > 31 || !wword_ptr_admissible(addr) then 
                this.(ok := false)
            else
                var value := read_reg256(WDR(di));
                var s := if grs1_inc then write_reg32(grs1, bv32_ops.add(base, 32)) else this;
                var l := if grs2_inc then s.write_reg32(grs2, di + 1) else s;
                l.write_wword(addr, value)
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
            shift_qws: uint2, fg: uint1): state
        {
            var v1 := read_reg256(wrs1);
            var v2 := read_reg256(wrs2);
            var v3 := read_reg256(WACC);
            var z := read_reg256(wrd);
            var flags := get_fgroup(fgroups, fg);

            var product := otbn_mulqacc(zero, v1, qwsel1, v2, qwsel2, shift_qws, v3);

            var mulqacc_so_result_t(new_acc, new_z, new_flags) :=
                otbn_mulqacc_so(product, z, lower, flags);

            write_flags(fg, new_flags).
            write_reg256(WACC, new_acc).
            write_reg256(wrd, new_z)
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

        function method eval_BN_NOT(wrd: reg256_t, wrs: reg256_t, shift: shift_t, fg: uint1): state
        {
            var v := read_reg256(wrs);
            var carry := read_flag(fg, 0);
            var (result, flags) := otbn_not(v, shift, carry);
            write_reg256(wrd, result).write_flags(fg, flags)
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
                var s := (if grd_inc then write_reg32(grd, di + 1) else this);
                var l := (if grs_inc then s.write_reg32(grs, si + 1) else s);
                l.write_reg256(WDR(di), read_reg256(WDR(si)))
        }

        function method eval_BN_WSRR(wrd: reg256_t, wsr: uint2): state
        {
            var val := if wsr == 0 then wmod
                else if wsr == 1 then 0x99999999_99999999_99999999_99999999_99999999_99999999_99999999_99999999
                else if wsr == 2 then 0x99999999_99999999_99999999_99999999_99999999_99999999_99999999_99999999
                else wacc;
            write_reg256(wrd, val)
        }

        function method eval_ins32(xins: ins32): state
        {
            if !ok then
                this
            else match xins
                case ADD(xrd, xrs1, xrs2) => eval_ADD(xrd, xrs1, xrs2)
                case ADDI(xrd, xrs1, imm) => eval_ADDI(xrd, xrs1, imm)
                case LW(xrd, offset, xrs1) => eval_LW(xrd, offset, xrs1)
                case SW(xrs2, offset, xrs1) => eval_SW(xrs2, offset, xrs1)
                case LI(xrd, imm32) => eval_LI(xrd, imm32)
                case ECALL => this
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
                case BN_MULQACC_SO(zero, wrd, lower, wrs1, qwsel1, wrs2, qwsel2, shift_qws, fg) =>
                    eval_BN_MULQACC_SO(zero, wrd, lower, wrs1, qwsel1, wrs2, qwsel2, shift_qws, fg)
                case BN_SUB(wrd, wrs1, wrs2, shift, fg) => 
                    eval_BN_SUB(wrd, wrs1, wrs2, shift, fg)
                case BN_SUBB(wrd, wrs1, wrs2, shift, fg) => 
                    eval_BN_SUBB(wrd, wrs1, wrs2, shift, fg)
                case BN_NOT(wrd, wrs, shift, fg) => 
                    eval_BN_NOT(wrd, wrs, shift, fg)
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
                case BN_WSRR(wrd, wsr) => 
                    eval_BN_WSRR(wrd, wsr)
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
                case Function(name, body) => eval_block(body)
                case Comment(com) => this
        }

    }

    predicate valid_state(s: state)
    {
        && s.ok
    }
}
