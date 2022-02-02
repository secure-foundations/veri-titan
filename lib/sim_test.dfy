include "../std_lib/src/Collections/Sequences/LittleEndianNat.dfy"
include "../std_lib/src/BoundedInts.dfy"

abstract module FW
{
    import BVSEQ: LittleEndianNat
    import Mul
    import DivMod

    function method BASE(): nat
    {
        BVSEQ.BASE()
    }

    // half word base
    function method HW_BASE(): nat
        ensures 1 < HW_BASE() < BVSEQ.BASE()
        ensures HW_BASE() * HW_BASE() == BVSEQ.BASE()

    type u_full = BVSEQ.uint

    function fw_to_nat(xs: seq<u_full>): nat
    {
        BVSEQ.ToNatRight(xs)
    }

    lemma upper_half_bound_lemma(x: nat, base: nat, half_base: nat)
        requires x < base
        requires 1 < half_base
        requires base == half_base * half_base
        ensures 0 <= x / half_base < half_base
    {
        var lh, uh := x % half_base, x / half_base;

        DivMod.LemmaFundamentalDivMod(x, half_base);

        assert x == half_base * uh + lh;

        if uh > half_base {
            Mul.LemmaMulIsCommutativeAuto();
            Mul.LemmaMulInequalityAuto();
            assert false;
        }
        DivMod.LemmaDivPosIsPos(x, half_base);
    }

    function method {:opaque} lh(x: u_full): u_full
        ensures lh(x) < HW_BASE()
    {
        x % HW_BASE()
    }

    function method {:opaque} uh(x: u_full): u_full
        ensures uh(x) < HW_BASE()
    {
        upper_half_bound_lemma(x, BVSEQ.BASE(), HW_BASE());
        x / HW_BASE()
    }

    lemma half_split_lemma(x: u_full)
        ensures x == lh(x) + uh(x) * HW_BASE();
    {
        DivMod.LemmaFundamentalDivMod(x, HW_BASE());
        Mul.LemmaMulIsCommutativeAuto();
        reveal lh();
        reveal uh();
    }
}

abstract module HW
{
    import BVSEQ: LittleEndianNat
    type u_half = BVSEQ.uint

    function hw_to_nat(xs: seq<u_half>): nat
    {
        BVSEQ.ToNatRight(xs)
    }
}

abstract module induction 
{
    import opened FW
    import opened HW
    import opened Seq

    lemma {:axiom} size_relation()
        ensures FW.HW_BASE() == HW.BVSEQ.BASE()

    function half_split(x: u_full): (u_half, u_half)
    {
        size_relation();
        (lh(x), uh(x))
    }

    function {:opaque} bn_full_2_half(xs: seq<u_full>): seq<u_half>
    {
        if |xs| == 0 then
            []
        else
            var (lh, uh) := half_split(First(xs));
            [lh, uh] + bn_full_2_half(DropFirst(xs))
    }

    lemma bn_full_2_half_equiv_val(xs: seq<u_full>, ys: seq<u_half>)
        requires bn_full_2_half(xs) == ys;
        ensures fw_to_nat(xs) == hw_to_nat(ys);
    {
        reveal bn_full_2_half();
        if |xs| == 0 {
            assert fw_to_nat(xs) == 0 by {
                reveal FW.BVSEQ.ToNatRight();
            }
            assert hw_to_nat(ys) == 0 by {
                reveal HW.BVSEQ.ToNatRight();
            }
        } else {
            var x := First(xs);
            var (lh, uh) := half_split(x);
            var xs' := DropFirst(xs);
            var ys' := bn_full_2_half(xs');

            calc == {
                fw_to_nat(xs);
                {
                    reveal FW.BVSEQ.ToNatRight();
                }
                fw_to_nat(xs') * BASE() + x;
                {
                    bn_full_2_half_equiv_val(xs', ys');
                }
                hw_to_nat(ys') * BASE() + x;
                {
                    half_split_lemma(x);
                }
                hw_to_nat(ys') * BASE() + lh + uh * HW_BASE();
                {
                    Mul.LemmaMulIsAssociativeAuto();
                    size_relation();
                }
                hw_to_nat(ys') * HW_BASE() * HW_BASE() + lh + uh * HW_BASE();
                {
                    Mul.LemmaMulIsDistributiveAddOtherWayAuto();
                }
                (hw_to_nat(ys') * HW_BASE() + uh) * HW_BASE() + lh;
                {
                    size_relation();
                    reveal HW.BVSEQ.ToNatRight();
                }
                hw_to_nat([uh] + ys') * HW_BASE() + lh;
                {
                    size_relation();
                    reveal HW.BVSEQ.ToNatRight();
                    assert [lh] + [uh] + ys' == [lh] + ([uh] + ys');
                }
                hw_to_nat([lh] + [uh] + ys');
                {
                    assert ys == [lh] + [uh] + ys';
                }
                hw_to_nat(ys);
            }
        }
    }

    lemma bn_full_2_half_equiv_len(xs: seq<u_full>, ys: seq<u_half>)
        requires bn_full_2_half(xs) == ys;
        ensures |xs| * 2 == |ys|;

    const NUM_FW: nat;
    const NUM_HW := NUM_FW * 2;
    const Y: nat;
    const M: nat;
    const fm': u_full;
    const hm': u_half;

    function mm_full_rec(fxs: seq<u_full>): nat
    decreases |fxs|;
    {
        if |fxs| == 0 then
            0
        else
            var acc := mm_full_rec(DropFirst(fxs));
            var a_0 := acc % BASE();
            var y_0 := Y % BASE();
            var x_i := First(fxs);
            var u_i := ((a_0 + x_i * y_0) * fm') % BASE();
            var acc := (acc + x_i * Y + u_i * M) / BASE();
            Mul.LemmaMulNonnegativeAuto();
            DivMod.LemmaDivPosIsPosAuto();
            acc
    }

    function mm_half_rec(hxs: seq<u_half>): nat
    decreases |hxs|;
    {
        if |hxs| == 0 then
            0
        else
            var acc := mm_half_rec(DropFirst(hxs));
            var a_0 := acc % HW_BASE();
            var y_0 := Y % HW_BASE();
            var x_i := First(hxs);
            var u_i := ((a_0 + x_i * y_0) * hm') % HW_BASE();
            var acc := (acc + x_i * Y + u_i * M) / HW_BASE();
            Mul.LemmaMulNonnegativeAuto();
            DivMod.LemmaDivPosIsPosAuto();
            acc
    }

    lemma weird(fxs: seq<u_full>, hxs: seq<u_half>)
        requires bn_full_2_half(fxs) == hxs;
        ensures mm_full_rec(fxs) == mm_half_rec(hxs)
    {
        bn_full_2_half_equiv_len(fxs, hxs);

        if |fxs| == 0 {
            return;
        }

        var acc := mm_full_rec(DropFirst(fxs));
        var a_0 := acc % BASE();
        var y_0 := Y % BASE();
        var x_i := First(fxs);
        var u_i := ((a_0 + x_i * y_0) * fm') % BASE();

        var q := ((a_0 + x_i * y_0) * fm') / BASE();
        assert q * BASE() + u_i == (a_0 + x_i * y_0) * fm' by {
            DivMod.LemmaFundamentalDivMod((a_0 + x_i * y_0) * fm', BASE());
        }

        var acc_l := (acc + x_i * Y + u_i * M) / BASE();
        assume acc_l >= 0;
        
        DivMod.LemmaFundamentalDivMod(acc + x_i * Y + u_i * M, BASE());
        var r: nat :| acc_l * BASE() + r == acc + x_i * Y + u_i * M;

        var hxs_0 := DropFirst(hxs);

        var acc_1 := mm_half_rec(DropFirst(hxs_0));
        var a_0_1 := acc_1 % HW_BASE();
        var y_0_1 := Y % HW_BASE();
        var x_i_1 := First(hxs_0);

        var u_i_1 := ((a_0_1 + x_i_1 * y_0_1) * hm') % HW_BASE();
        var q_1 := ((a_0_1 + x_i_1 * y_0_1) * hm') / HW_BASE();

        assert q_1 * HW_BASE() + u_i_1 == (a_0_1 + x_i_1 * y_0_1) * hm' by {
            DivMod.LemmaFundamentalDivMod((a_0_1 + x_i_1 * y_0_1) * hm', HW_BASE());
        }

        var acc_0' := (acc_1 + x_i_1 * Y + u_i_1 * M) / HW_BASE();
        DivMod.LemmaFundamentalDivMod(acc_1 + x_i_1 * Y + u_i_1 * M, HW_BASE());
        var r_1: nat :| acc_0' * HW_BASE() + r_1 == acc_1 + x_i_1 * Y + u_i_1 * M;

        assert acc == acc_1 by {
            assume bn_full_2_half(DropFirst(fxs)) == DropFirst(hxs_0);
            weird(DropFirst(fxs), DropFirst(hxs_0));
        }

        var acc_0 := mm_half_rec(hxs_0);
        var a_0_0 := acc_0 % HW_BASE();
        var y_0_0 := Y % HW_BASE();
        var x_i_0 := First(hxs);

        var u_i_0 := ((a_0_0 + x_i_0 * y_0_0) * hm') % HW_BASE();
        var q_0 := ((a_0_0 + x_i_0 * y_0_0) * hm') / HW_BASE();

        assert q_0 * HW_BASE() + u_i_0 == (a_0_0 + x_i_0 * y_0_0) * hm' by {
            DivMod.LemmaFundamentalDivMod((a_0_0 + x_i_0 * y_0_0) * hm', HW_BASE());
        }

        var acc_r := (acc_0 + x_i_0 * Y + u_i_0 * M) / HW_BASE();
        DivMod.LemmaFundamentalDivMod(acc_0 + x_i_0 * Y + u_i_0 * M, HW_BASE());
        var r_0: nat :| acc_r * HW_BASE() + r_0 == acc_0 + x_i_0 * Y + u_i_0 * M;

        // assert q * BASE() + u_i == (a_0 + x_i * y_0) * fm';
        // assert q_0 * HW_BASE() + u_i_0 == (a_0_0 + x_i_0 * y_0_0) * hm'
        // assert q_1 * HW_BASE() + u_i_1 == (a_0_1 + x_i_1 * y_0_1) * hm';

        calc == {
            acc_r * HW_BASE() * HW_BASE();
            (acc_0 + x_i_0 * Y + u_i_0 * M - r_0) * HW_BASE();
            {
                assume false;
            }
            acc_0 * HW_BASE() + x_i_0 * Y * HW_BASE() + u_i_0 * M * HW_BASE() - r_0 * HW_BASE();
            {
                assert acc_0 == acc_0';
            }
            acc_1 + x_i_1 * Y + u_i_1 * M - r_1 + x_i_0 * Y * HW_BASE() + u_i_0 * M * HW_BASE() - r_0 * HW_BASE();
            {
                assume (x_i_1 + x_i_0 * HW_BASE()) * Y == x_i_1 * Y + x_i_0 * Y * HW_BASE();
            }
            acc_1 + (x_i_1 + x_i_0 * HW_BASE()) * Y + u_i_1 * M - r_1 + u_i_0 * M * HW_BASE() - r_0 * HW_BASE();
            {
                assume (u_i_1 + u_i_0 * HW_BASE()) * M == u_i_1 * M + u_i_0 * M * HW_BASE();
            }
            acc_1 + (x_i_1 + x_i_0 * HW_BASE()) * Y - r_1 + (u_i_1 + u_i_0 * HW_BASE()) * M - r_0 * HW_BASE();
            {
                assume x_i == x_i_1 + x_i_0 * HW_BASE();
            }
            acc_1 + x_i * Y - r_1 + (u_i_1 + u_i_0 * HW_BASE()) * M - r_0 * HW_BASE();
        }
        
        // acc_l * BASE() + r == acc + x_i * Y + u_i * M;

        // (acc_0 + x_i_0 * Y + u_i_0 * M) / HW_BASE();




        // Mul.LemmaMulNonnegativeAuto();
        // DivMod.LemmaDivPosIsPosAuto();

        assume false;
    }
}
