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
            var (lh, uh) := half_split(Last(xs));
            bn_full_2_half(DropLast(xs)) + [lh, uh]
    }

/*
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
            var x := Last(xs);
            var (lh, uh) := half_split(x);
            var xs' := DropLast(xs);
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
*/

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
    {
        if |fxs| == 0 then
            0
        else
            var A := mm_full_rec(DropLast(fxs));
            var a := A % BASE();
            var y := Y % BASE();
            var x := Last(fxs);
            var u_i := ((a + x * y) * fm') % BASE();
            var A := (A + x * Y + u_i * M) / BASE();
            Mul.LemmaMulNonnegativeAuto();
            DivMod.LemmaDivPosIsPosAuto();
            A
    }

    function mm_half_rec(hxs: seq<u_half>): nat
    decreases |hxs|;
    {
        if |hxs| == 0 then
            0
        else
            var A := mm_half_rec(DropLast(hxs));
            var a := A % HW_BASE();
            var y := Y % HW_BASE();
            var x := Last(hxs);
            var u_i := ((a + x * y) * hm') % HW_BASE();
            var A := (A + x * Y + u_i * M) / HW_BASE();
            Mul.LemmaMulNonnegativeAuto();
            DivMod.LemmaDivPosIsPosAuto();
            A
    }

    lemma weird(fxs: seq<u_full>, hxs: seq<u_half>)
        requires bn_full_2_half(fxs) == hxs;
        ensures mm_full_rec(fxs) == mm_half_rec(hxs)
    {
        bn_full_2_half_equiv_len(fxs, hxs);

        if |fxs| == 0 {
            return;
        }

        var A := mm_full_rec(DropLast(fxs));
        var a := A % BASE();
        var y := Y % BASE();
        var x := Last(fxs);
        var u := ((a + x * y) * fm') % BASE();
        var A_l := (A + x * Y + u * M) / BASE();
        assume A_l * BASE() == (A + x * Y + u * M);

        // assert A_l == mm_full_rec(fxs);

        var A_0 := mm_half_rec(DropLast(DropLast(hxs)));

        assert A == A_0 by {
            reveal bn_full_2_half();
            assert bn_full_2_half(DropLast(fxs)) == DropLast(DropLast(hxs));
            weird(DropLast(fxs), DropLast(DropLast(hxs)));
        }

        var a_0 := A % HW_BASE();
        var y_0 := Y % HW_BASE();
        var x_0 := Last(DropLast(hxs));
        var u_0 := ((a_0 + x_0 * y_0) * hm') % HW_BASE();
        var A_1 := (A + x_0 * Y + u_0 * M) / HW_BASE();
        assume A_1 *  HW_BASE() == (A + x_0 * Y + u_0 * M);

        // assert A_1 == mm_half_rec(DropLast(hxs));

        var a_1 := A_1 % HW_BASE();
        var x_1 := Last(hxs);
        var u_1 := ((a_1 + x_1 * y_0) * hm') % HW_BASE();
        var A_r := (A_1 + x_1 * Y + u_1 * M) / HW_BASE();
        assume A_r * HW_BASE() == A_1 + x_1 * Y + u_1 * M;

        // assert A_r == mm_half_rec(hxs);

        assert x_1 * HW_BASE() + x_0 == x by {
            reveal bn_full_2_half();
            var (lh, uh) := half_split(x);
            assert bn_full_2_half(DropLast(fxs)) + [lh, uh] == hxs;
            assert x_1 == Last(hxs);
            assert x_0 == Last(DropLast(hxs));
            half_split_lemma(x);
        }

        calc == {
            A_r * BASE();
            {
                Mul.LemmaMulIsAssociativeAuto();
            }
            A_r * HW_BASE() * HW_BASE();
            (A_1 + x_1 * Y + u_1 * M) * HW_BASE();
            {
                Mul.LemmaMulIsDistributiveAddOtherWayAuto();
            }
            A_1 * HW_BASE() + x_1 * Y * HW_BASE() + u_1 * M * HW_BASE();
            A + x_0 * Y + u_0 * M + x_1 * Y * HW_BASE() + u_1 * M * HW_BASE();
            {
                Mul.LemmaMulIsAssociativeAuto();
                assert x_1 * Y * HW_BASE() == x_1 * HW_BASE() * Y;
            }
            A + x_0 * Y + u_0 * M + x_1 * HW_BASE() * Y + u_1 * M * HW_BASE();
            A + x_0 * Y + x_1 * HW_BASE() * Y + u_0 * M + u_1 * M * HW_BASE();
            {
                Mul.LemmaMulIsDistributiveAddOtherWayAuto();
                assert (x_0 + x_1 * HW_BASE()) * Y == x_0 * Y + x_1 * HW_BASE() * Y;
            }
            A + (x_0 + x_1 * HW_BASE()) * Y + u_0 * M + u_1 * M * HW_BASE();
            {
                assert x_0 + x_1 * HW_BASE() == x;
            }
            A + x * Y + u_0 * M + u_1 * M * HW_BASE();
            {
                Mul.LemmaMulIsAssociativeAuto();
            }
            A + x * Y + u_0 * M + u_1 * HW_BASE() * M;
            {
                Mul.LemmaMulIsDistributiveAddOtherWayAuto();
            }
            A + x * Y + (u_0 + u_1 * HW_BASE()) * M;
            {
                assume u_0 + u_1 * HW_BASE() == u;
            }
            A + x * Y + u * M;
            A_l * BASE();
        }

        assert A_r == A_l by {
            assert A_r * BASE() == A_l * BASE();
            Mul.LemmaMulEqualityConverse(BASE(), A_r, A_l);
        }
    }
}
