include "../../lib/bv_ops.dfy"

module ot_machine {
    import opened bv_ops

    const DMEM_LIMIT: int := 0x8000
    const NUM_WORDS:  int := 12

    // ignore the mapping
    const NA :int := -1;

/* registers definions */

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


/* flags definions */

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

/* instruction definions */

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

    function mod_add(a: nat, b: nat, m: nat): nat 
        requires a < m && b < m;
    {
        if a + b > m then a + b - m else a + b
    }

    function method set_mlz_flags(carry: uint1, value: uint256): flags_t
    {
        flags_t(carry == 1, uint256_msb(value) == 1, uint256_lsb(value) == 1, value == 0)
    }

    function method otbn_addc(x: uint256, y: uint256, shift: shift_t, carry: bool) : (uint256, flags_t)
    {
        var cin := if carry then 1 else 0;
        var (sum, cout) := uint256_addc(x, uint256_sb(y, shift), cin);
        (sum, set_mlz_flags(cout, sum))
    }

    function method otbn_subb(x: uint256, y: uint256, shift: shift_t, borrow: bool) : (uint256, flags_t)
    {
        var cf := if borrow then 1 else 0;
        var (diff, cout) := uint256_subb(x, uint256_sb(y, shift), cf);
        (diff, set_mlz_flags(cout, diff))
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
        if zero then shift else (acc + shift) % BASE_256
    }

    predicate otbn_mulqacc_is_safe(shift: uint2, acc: uint256)
    {
        // make sure no overflow from shift (product needs to be 128 bits)
        && (shift <= 2) 
        // make sure no overflow from addtion
        && (acc + otbn_qshift_safe(BASE_128 - 1, shift) < BASE_256)
    }

    // quater shift but no overflow
    function otbn_qshift_safe(x: uint256, q: uint2): (r: uint256)
        requires (q == 1) ==> (x < BASE_192);
        requires (q == 2) ==> (x < BASE_128);
        requires (q == 3) ==> (x < BASE_64);
    {
        if q == 0 then x
        else if q == 1 then x * BASE_64
        else if q == 2 then x * BASE_128
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

    datatype mulqacc_so_result_t = mulqacc_so_result_t(
        new_acc: uint256,
        new_dst: uint256,
        new_flags: flags_t)

    function method otbn_mulqacc_so(product: uint256, z: uint256, lower: bool, flags: flags_t) : mulqacc_so_result_t
    {
        var lh, uh := uint256_lh(product), uint256_uh(product);
        var new_flags :=
            (if lower then
                flags_t(flags.cf, flags.msb, uint128_lsb(lh) == 1, lh == 0)
            else
                flags_t(flags.cf, uint128_msb(lh) == 1, flags.lsb, (lh == 0) && flags.zero));
        mulqacc_so_result_t(uh, uint256_hwb(z, lh, lower), new_flags)
    }

    function method otbn_not(x: uint256, shift: shift_t, carry: bool): (uint256, flags_t)
    {
        var result := uint256_not(uint256_sb(x, shift));
        // keep the old carry
        (result, set_mlz_flags(bool_to_uint1(carry), result))
    }

    function method otbn_xor(x: uint256, y: uint256, shift: shift_t, carry: bool): (uint256, flags_t)
    {
        var result := uint256_xor(x, uint256_sb(y, shift));
        // keep the old carry
        (result, set_mlz_flags(bool_to_uint1(carry), result))
    }

    function method otbn_sel(x: uint256, y: uint256, sel: bool): uint256
    {
        if sel then x else y
    }

    function method wwrod_offset_ptr(base: uint32, offset: int10): uint32
    {
        uint32_addi(base, offset * 32)
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
        uint256_eighth_assemble(p0, p1, p2, p3, p4, p5, p6, p7)
    }

    function method mem_write_wword(mem: mem_t, ptr: nat, value: uint256): (mem' : mem_t)
        requires wword_ptr_admissible(ptr)
        ensures wword_ptr_valid(mem', ptr)
    {
        mem[ptr + 0 := uint256_eighth_split(value, 0)]
            [ptr + 4 := uint256_eighth_split(value, 1)]
            [ptr + 8 := uint256_eighth_split(value, 2)]
            [ptr + 12 := uint256_eighth_split(value, 3)]
            [ptr + 16 := uint256_eighth_split(value, 4)]
            [ptr + 20 := uint256_eighth_split(value, 5)]
            [ptr + 24 := uint256_eighth_split(value, 6)]
            [ptr + 28 := uint256_eighth_split(value, 7)]
    }

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
            uint256_eighth_assemble(p0, p1, p2, p3, p4, p5, p6, p7)
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
            var sum := uint32_add(v1, v2);
            write_reg32(xrd, sum)
        }

        function method eval_ADDI(xrd: reg32_t, xrs1: reg32_t, imm: int12): state
        {
            var v1 := read_reg32(xrs1);
            var sum := uint32_addi(v1, imm);
            write_reg32(xrd, sum)
        }

        function method eval_LW(xrd: reg32_t, offset: int12, xrs1: reg32_t): state
        {
            var base := read_reg32(xrs1);
            var addr := uint32_addi(base, offset);
            if !xword_ptr_admissible(addr) then this.(ok := false)
            else write_reg32(xrd, read_xword(addr))
        }

        function method eval_SW(xrs2: reg32_t, offset: int12, xrs1: reg32_t): state
        {
            var base := read_reg32(xrs1);
            var addr := uint32_addi(base, offset);
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
                var l := (if grs_inc then s.write_reg32(grs, uint32_add(base, 32)) else s);
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
                var s := if grs1_inc then write_reg32(grs1, uint32_add(base, 32)) else this;
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
                case Comment(com) => this
        }

        method dump_regs()
        {
            var i := 0;
            while i < 32
            {
                print(" x"); print(i); 
                if i < 10 {
                    print("  = ");
                } else {
                    print(" = ");
                }
                print_as_hex(read_reg32(GPR(i)), 4); print("\n"); 
                i := i + 1;
            }

            i := 0;
            while i < 32
            {
                print(" w"); print(i);
                if i < 10 {
                    print("  = ");
                } else {
                    print(" = ");
                }
                print_as_hex(read_reg256(WDR(i)), 32); print("\n"); 
                i := i + 1;
            }

            print(" fg0 = ");print_as_hex(fgroups.fg0.to_nat(), 4); print("\n"); 
            print(" fg1 = ");print_as_hex(fgroups.fg1.to_nat(), 4); print("\n"); 
        }

        method dump_mem(addr: uint32, words: uint32)
            requires xword_ptr_admissible(addr + words * 4)
        {
            var end := addr + words * 4;
            var cur := addr;
            var i := 0;

            while cur < end
                invariant cur == addr + i * 4
                invariant xword_ptr_admissible(cur)
                decreases end - cur
            {
                var value := read_xword(cur);
                print(cur); print(":"); print_as_hex(value, 4); print("\n");
                cur := cur + 4;
                i := i + 1;
            }
        }
    }

    method print_as_hex(a: nat, bytes: nat)
    {
        var val := a;
        var num_digits := bytes * 2;
        var i := 0;
        var result := "";
        while i < num_digits
            decreases num_digits - i
        {
            var digit := val % 16;
            if digit == 0 {
                result := "0" + result;
            } else if digit == 1 {
                result := "1" + result;
            } else if digit == 2 {
                result := "2" + result;
            } else if digit == 3 {
                result := "3" + result;
            } else if digit == 4 {
                result := "4" + result;
            } else if digit == 5 {
                result := "5" + result;
            } else if digit == 6 {
                result := "6" + result;
            } else if digit == 7 {
                result := "7" + result;
            } else if digit == 8 {
                result := "8" + result;
            } else if digit == 9 {
                result := "9" + result;
            } else if digit == 10 {
                result := "a" + result;
            } else if digit == 11 {
                result := "b" + result;
            } else if digit == 12 {
                result := "c" + result;
            } else if digit == 13 {
                result := "d" + result;
            } else if digit == 14 {
                result := "e" + result;
            } else if digit == 15 {
                result := "f" + result;
            }
            val := val / 16;
            i := i + 1;
        }
        print("0x"); print(result);
    }

    predicate valid_state(s: state)
    {
        && s.ok
    }
}
