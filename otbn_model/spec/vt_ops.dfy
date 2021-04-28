include "vt_types.dfy"
include "vt_consts.dfy"
include "bv_ops.dfy"
include "../lib/powers.dfy"

module vt_ops {
    import opened vt_types
    import opened bv_ops
    import opened vt_consts
    import opened powers

    function eval_reg32(s: state, r: reg32_t) : uint32
    {
        s.gprs[r.index]
    }

    predicate evalIns32(xins: ins32, s: state, r: state)
    {
        if !s.ok then
            !r.ok
        else
            r.ok && (valid_state(s) ==> valid_state(r))
    }

    function eval_reg256(s: state, r: reg256_t) : uint256
    {
        match r {
            case WDR(index) => s.wdrs[r.index]
            case WMOD => s.wmod
            case WRND => s.wrnd
            case WACC => s.wacc
        }
    }

    predicate eval_ins256(wins: ins256, s: state, r: state)
    {
        if !s.ok then
            !r.ok
        else
            r.ok && (valid_state(s) ==> valid_state(r))
    }

    predicate evalBlock(block: codes, s: state, r: state)
    {
        if block.CNil? then
            r == s
        else
            exists r': state :: evalCode(block.hd, s, r') && evalBlock(block.tl, r', r)
    }

    function eval_cond(s: state, wc: whileCond): nat
    {
        match wc 
            case RegCond(r) => eval_reg32(s, r)
            case ImmCond(c) => c
    }

    predicate evalWhile(c: code, n: nat, s: state, r: state)
        decreases c, n
    {
        if s.ok then
            if n == 0 then
                s == r
            else
                exists loop_body_end: state :: evalCode(c, s, loop_body_end)
                    && evalWhile(c, n - 1, loop_body_end, r)
        else
            !r.ok
    }

    predicate evalCode(c: code, s: state, r: state)
        decreases c, 0
    {
        match c
            case Ins32(ins) => evalIns32(ins, s, r)
            case Ins256(ins) => eval_ins256(ins, s, r)
            case Block(block) => evalBlock(block, s, r)
            //case IfElse(cond, ifT, ifF) => evalIfElse(cond, ifT, ifF, s, r)
            case While(cond, body) => evalWhile(body, eval_cond(s, cond), s, r)
    }

    function select_fgroup(fgps: fgroups_t, which: uint1): flags_t
    {
        if which == 0 then fgps.fg0 else fgps.fg1
    }

    function get_flag(fgps: fgroups_t, which_group: uint1, which_flag: uint2) : bool
    {
        if which_flag == 0 then select_fgroup(fgps, which_group).cf 
        else if which_flag == 1 then select_fgroup(fgps, which_group).msb
        else if which_flag == 2 then select_fgroup(fgps, which_group).lsb
        else select_fgroup(fgps, which_group).zero
    }

    function get_cf0(fgps: fgroups_t): bool
    {
        select_fgroup(fgps, 0).cf 
    }

    function get_cf1(fgps: fgroups_t): bool
    {
        select_fgroup(fgps, 1).cf 
    }

    function update_fgroups(fgps: fgroups_t, which_group: uint1, new_flags_t: flags_t) : fgroups_t
    {
        if which_group == 0 then fgps.(fg0 := new_flags_t) else fgps.(fg1 := new_flags_t)
    }

    function otbn_addc(x: uint256, y: uint256, shift: shift_t, carry: bool) : (uint256, flags_t)
    {
        var cin := if carry then 1 else 0;
        var (sum, cout) := uint256_addc(x, uint256_sb(y, shift), cin);
        // TODO: MSB/LSB
        var fg := flags_t(cout == 1, false, false, sum == 0);
        (sum, fg)
    }

    // function otbn_addm(x: uint256, y: uint256, mod: uint256) : uint256
    // {
    //     var (sum, _) := otbn_add_carray(x, y, false);
    //     if sum >= mod then sum - mod else sum
    // }

    function otbn_subb(x: uint256, y: uint256, shift: shift_t, borrow: bool) : (uint256, flags_t)
    {
        var cf := if borrow then 1 else 0;
        var (diff, cout) := uint256_subb(x, uint256_sb(y, shift), cf);
        // TODO: MSB/LSB
        var fg := flags_t(cout == 1, false, false, diff == 0);
        (diff, fg)
    }

    // function otbn_subm(x: uint256, y: uint256, wmod: uint256) : uint256
    //     requires false;
    // {
    //     // FIXME: some bound checking?
    //     assume false;
    //     var result := (x as bv256 - y as bv256) as uint256;
    //     if result >= wmod then (result as bv256 - wmod as bv256) as uint256 else result
    // }

    function otbn_mulqacc(
        zero: bool,
        x: uint256, qx: uint2,
        y: uint256, qy: uint2,
        shift: uint2,
        acc: uint256) : uint256
    {
        var product := uint256_qmul(x, qx, y, qy);
        var shift := uint256_ls(product, shift * 8);
        if zero then shift else (acc + shift) % BASE_256
    }

    predicate otbn_mulqacc_is_safe(shift: uint2, acc: uint256)
    {
        // make sure no overflow from shift (product is assumed to be 128 bits)
        && (shift <= 2) 
        // make sure no overflow from addtion
        && (acc + otbn_qshift_safe(BASE_128 - 1, shift) < BASE_256)
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

    function otbn_xor(x: uint256, y: uint256, shift: shift_t) : uint256
    {
        uint256_xor(x, uint256_sb(y, shift))
    }

    function otbn_or(x: uint256, y: uint256, shift: shift_t) : uint256
    {
        uint256_or(x, uint256_sb(y, shift))
    }
            
    function otbn_and(x: uint256, y: uint256, shift: shift_t) : uint256
    {
        uint256_and(x, uint256_sb(y, shift))
    }

    function otbn_rshi(x: uint256, y: uint256, shift_amt: int) : uint256
        requires 0 <= shift_amt < 256;
    {
        var concat : int := x * BASE_256 + y;
        (concat / pow2(shift_amt)) % BASE_256
    }

    function to_nat(xs: seq<uint256>): nat
    {
        if |xs| == 0 then 0
        else
            var len' := |xs| - 1;
            to_nat(xs[..len']) + xs[len'] * power(BASE_256, len')
    }

    lemma to_nat_singleton_lemma(xs: seq<uint256>)
        requires |xs| == 1
        ensures to_nat(xs) == xs[0]
    {
        reveal power();
    }

    lemma to_nat_pair_lemma(xs: seq<uint256>)
        requires |xs| == 2
        ensures to_nat(xs) == xs[0] + xs[1] * BASE_256
    {
        to_nat_singleton_lemma(xs[..1]);
        reveal power();
    }

    lemma to_nat_zero_extend_lemma(xs': seq<uint256>, xs: seq<uint256>) 
        requires |xs'| < |xs|
        requires var len' := |xs'|;
            && xs[..len'] == xs'
            && xs[len'.. ] == seq(|xs| - len', i => 0)
        ensures to_nat(xs') == to_nat(xs);
    {
        var len, len' := |xs|, |xs'|;
        if len != len' + 1 {
            var len'' := len-1;
            calc == {
                to_nat(xs);
                to_nat(xs[..len'']) + xs[len''] * power(BASE_256, len'');
                to_nat(xs[..len'']);
                {
                    to_nat_zero_extend_lemma(xs', xs[..len'']);
                }
                to_nat(xs');
            }
        }
    }

    function seq_addc(xs: seq<uint256>, ys: seq<uint256>) : (seq<uint256>, uint1)
        requires |xs| == |ys|
        ensures var (zs, cout) := seq_addc(xs, ys);
            && |zs| == |xs|
    {
        if |xs| == 0 then ([], 0)
        else 
            var len' := |xs| - 1;
            var (zs', cin) := seq_addc(xs[..len'], ys[..len']);
            var (z, cout) := uint256_addc(xs[len'], ys[len'], cin);
            (zs' + [z], cout)
    }

    lemma seq_addc_to_nat_lemma(
        xs: seq<uint256>, ys: seq<uint256>, zs: seq<uint256>, cout: uint1)
        requires |xs| == |ys|;
        requires seq_addc(xs, ys) == (zs, cout);
        ensures to_nat(xs) + to_nat(ys) == to_nat(zs) + power(BASE_256, |xs|) * cout;
    {
        if |xs| == 0 {
            reveal power();
        } else {
            var len, len' := |xs|,|xs| - 1;
            var xs', ys' := xs[..len'], ys[..len'];
            var x, y := xs[len'], ys[len'];
    
            var (zs', cin) := seq_addc(xs', ys');
            var (z, _) := uint256_addc(x, y, cin);

            var weight' := power(BASE_256, len');

            calc {
                to_nat(zs) + power(BASE_256, len) * cout;
                { assert to_nat(zs) == to_nat(zs') + z * weight'; }
                to_nat(zs') + z * weight' + power(BASE_256, len) * cout;
                { reveal power(); }
                to_nat(zs') + z * weight' + weight' * BASE_256 * cout;
                to_nat(zs') + z * weight' + cout * BASE_256 * weight' ;
                {
                   assert x * weight' + y * weight' + cin as int * weight'
                    == z * weight' + cout * BASE_256 * weight' by {
    		            assert x + y + cin as int == z + cout * BASE_256;
                    }
                }
                to_nat(zs') + x * weight' + y * weight' + cin as int * weight';
                {
                    assert to_nat(zs') + weight' * cin as nat
                    == to_nat(xs') + to_nat(ys') by {
                        seq_addc_to_nat_lemma(xs', ys', zs', cin);
                    }
                }
                to_nat(xs') + to_nat(ys')+ x * weight' + y * weight';
                to_nat(xs) + to_nat(ys);
            }
        }
    }

    lemma seq_addc_len1_lemma(
        x: uint256, y: uint256, z: uint256, c: uint1)
        requires (z, c) == uint256_addc(x, y, 0);
        ensures seq_addc([x], [y]) == ([z], c);
    {
        assert [] + [z] == [z];
    }

    lemma seq_addc_len2_lemma(
        x0: uint256, y0: uint256, z0: uint256, c0: uint1,
        x1: uint256, y1: uint256, z1: uint256, c1: uint1)
        requires (z0, c0) == uint256_addc(x0, y0, 0);
        requires (z1, c1) == uint256_addc(x1, y1, c0);
        ensures seq_addc([x0, x1], [y0, y1]) == ([z0, z1], c1);
    {
        seq_addc_len1_lemma(x0, y0, z0, c0);
        assert [z0] + [z1] == [z0, z1];
    }

    function seq_subb(xs: seq<uint256>, ys: seq<uint256>) : (seq<uint256>, uint1)
        requires |xs| == |ys|
        ensures var (zs, cout) := seq_subb(xs, ys);
            && |zs| == |xs|
    {
        if |xs| == 0 then ([], 0)
        else 
            var len' := |xs| - 1;
            var (zs, bin) := seq_subb(xs[..len'], ys[..len']);
            var (z, bout) := uint256_subb(xs[len'], ys[len'], bin);
            (zs + [z], bout)
    }

/*
    lemma lemma_extend_seq_subb(
            xs: seq<uint256>, ys: seq<uint256>, zs: seq<uint256>, 
            cin :uint1, cout:uint1,
            x:uint256, y:uint256, z:uint256)
        requires |xs| == |ys|
        requires (zs, cin) == seq_subb(xs, ys)
        requires (z, cout) == uint256_subb(x, y, cin)
        ensures (zs + [z], cout) == seq_subb(xs + [x], ys + [y])
    {
    }

    lemma lemma_empty_seq_subb()
        ensures ([], 0) == seq_subb([], [])
    {
    }
*/

}