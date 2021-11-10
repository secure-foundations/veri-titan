include "generic_bv_ops.dfy"
include "bv256_ops.dfy"
include "../arch/otbn/machine.s.dfy"

abstract module generic_mm_lemmas {
    import opened GBV: generic_bv_ops

    import opened Mul
    import opened Power
    import opened DivMod
    import opened integers

    type uint = GBV.BVSEQ.uint

    const NUM_WORDS: nat

    function to_nat(xs: seq<uint>): nat
    {
        GBV.BVSEQ.ToNatRight(xs)
    }

    function BASE(): nat
    {
        GBV.BVSEQ.BASE()
    }

    predicate cong_BASE(x: int, y: int)
    {
        IsModEquivalent(x, y, BASE())
    }

    function pow_BASE(e: nat): nat
    {
        LemmaPowPositiveAuto();
        Pow(BASE(), e)
    }

/* begin section on RSA invariant */

   datatype rsa_params = rsa_params(
        M: nat, M0D: uint,
        R: nat, RR: nat, R_INV: nat,
        E: nat, E0: nat,
        SIG: nat,
        BASE_INV: nat)

    predicate rsa_params_inv(rsa: rsa_params)
    {
        // E0 is derived from the exponent E
        && rsa.E == Pow(2, rsa.E0) + 1
        // modulo is none zero
        && rsa.M != 0
        && cong_BASE(rsa.M0D * rsa.M, -1)
        // signature
        && 0 < rsa.SIG < rsa.M
        && rsa.R == pow_BASE(NUM_WORDS)
        && rsa.RR < rsa.M
        && IsModEquivalent(rsa.RR, rsa.R * rsa.R, rsa.M)
        && rsa.R_INV == Pow(rsa.BASE_INV, NUM_WORDS)
        && IsModEquivalent(rsa.R_INV * rsa.R, 1, rsa.M)
        && IsModEquivalent(GBV.BVSEQ.BASE() * rsa.BASE_INV, 1, rsa.M)
    }

/* end section on RSA invariant */

/* begin section on double word addtion */

    datatype dw_view_raw = dw_view_cons(
        lh: uint, uh: uint, full: nat)

    type dw_view_t = num: dw_view_raw |
        && num.full < DW_BASE()
        && num.lh == dw_lh(num.full)
        && num.uh == dw_uh(num.full)
        witness *

    lemma dw_view_lemma(num: dw_view_t)
        ensures num.full
        == to_nat([num.lh, num.uh])
        == num.lh + num.uh * BASE();
    {
        assume false;
    }

    predicate dw_add_is_safe(
        x_lh: uint, x_uh: uint,
        y_lh: uint, y_uh: uint)
    {
        to_nat([x_lh, x_uh]) + to_nat([y_lh, y_uh]) < DW_BASE()
    }

    lemma dw_add_lemma(
        x_lh: uint, x_uh: uint,
        y_lh: uint, y_uh: uint,
        c1: uint1, c2: uint1,
        z_lh: uint, z_uh: uint)
    returns (z: dw_view_t)

        requires dw_add_is_safe(x_lh, x_uh, y_lh, y_uh);
        requires (z_lh, c1) == GBV.addc(x_lh, y_lh, 0);
        requires (z_uh, c2) == GBV.addc(x_uh, y_uh, c1);
        
        ensures z.full == to_nat([z_lh, z_uh]) == to_nat([x_lh, x_uh]) + to_nat([y_lh, y_uh]);
        ensures z.lh ==  z_lh;
        ensures z.uh ==  z_uh;
    {
        var x_full := to_nat([x_lh, x_uh]);
        var y_full := to_nat([y_lh, y_uh]);
        var z_full := to_nat([z_lh, z_uh]);

        assert GBV.BVSEQ.SeqAdd([x_lh], [y_lh]) == ([z_lh], c1) by {
            reveal GBV.BVSEQ.SeqAdd();
            assert [] + [z_lh] == [z_lh];
        }

        assert GBV.BVSEQ.SeqAdd([x_lh, x_uh], [y_lh, y_uh]) == ([z_lh, z_uh], c2) by {
            reveal BVSEQ.SeqAdd();
            assert [z_lh] + [z_uh] == [z_lh, z_uh];
        }

        assert to_nat([z_lh, z_uh]) + c2 * Pow(GBV.BVSEQ.BASE(), 2) == x_full + to_nat([y_lh, y_uh]) by {
            GBV.BVSEQ.LemmaSeqAdd([x_lh, x_uh], [y_lh, y_uh], [z_lh, z_uh], c2);
        }

        if c2 != 0 {
            reveal Pow();
            assert false;
        }

        var full := to_nat([z_lh, z_uh]);

        assert z_lh + z_uh * BASE() == full by {
            GBV.BVSEQ.LemmaSeqLen2([z_lh, z_uh]);
        }

        LemmaFundamentalDivModConverse(full, BASE(), z_uh, z_lh);

        assert z_lh == dw_lh(full) by {
            reveal dw_lh();
        }
        assert z_uh == dw_uh(full) by {
            reveal dw_uh();
        }

        z := dw_view_cons(z_lh, z_uh, full);
    }

    // method dw_add(x_lh: uint, x_uh: uint, y_lh: uint, y_uh: uint)
    //     requires dw_add_is_safe(x_lh, x_uh, y_lh, y_uh);
    // {
    //     var (z_lh, c1) := GBV.addc(x_lh, y_lh, 0);
    //     var (z_uh, c2) := GBV.addc(x_uh, y_uh, c1);
    //     dw_add_lemma(x_lh, x_uh, y_lh, y_uh, c1, c2, z_lh, z_uh);
    // }

/* end section on double word addtion */

/* begin section on multi word subtraction */

    function seq_sub(x: seq<uint>, y: seq<uint>): (seq<uint>, uint)
        requires |x| == |y|
    {
        GBV.BVSEQ.SeqSub(x, y)
    }

    predicate subb_inv(
        dst: seq<uint>,
        carry: uint1,
        src1: seq<uint>,
        src2: seq<uint>,
        index: nat)
    requires |dst| == |src1| == |src2|;
    requires index <= |src1|;
    {
        (dst[..index], carry)
            == seq_sub(src1[..index], src2[..index])
    }

    lemma subb_inv_pre_lemma(
        dst: seq<uint>,
        src1: seq<uint>,
        src2: seq<uint>)
    requires |dst| == |src1| == |src2|;
    ensures subb_inv(dst, 0, src1, src2, 0)
    {
        reveal GBV.BVSEQ.SeqSub();
    }

    lemma subb_inv_peri_lemma(
        dst: seq<uint>,
        new_carry: uint1,
        src1: seq<uint>,
        src2: seq<uint>,
        old_carry: uint1,
        index: nat)

    requires |dst| == |src1| == |src2|;
    requires index < |src1|;
    requires subb_inv(dst, old_carry, src1, src2, index);
    requires (dst[index], new_carry)
        == GBV.subb(src1[index], src2[index], old_carry);
    ensures subb_inv(dst, new_carry, src1, src2, index + 1);
    {
        reveal GBV.BVSEQ.SeqSub();
        var (zs, bin) := seq_sub(src1[..index], src2[..index]);
        var (z, bout) := GBV.subb(src1[index], src2[index], old_carry);

        assert dst[..index+1] == zs + [z];
        assert src1[..index+1] == src1[..index] + [src1[index]];
        assert src2[..index+1] == src2[..index] + [src2[index]];
    }

    lemma subb_inv_post_lemma(
        dst: seq<uint>,
        carry: uint1,
        src1: seq<uint>,
        src2: seq<uint>)

    requires |dst| == |src1| == |src2|;
    requires subb_inv(dst, carry, src1, src2, |dst|);
    ensures to_nat(dst) == to_nat(src1) - to_nat(src2) + carry * pow_BASE(|dst|);
    ensures carry == 0 <==> to_nat(src1) >= to_nat(src2)
    {
        var index := |dst|;
        assert dst[..index] == dst;
        assert src1[..index] == src1;
        assert src2[..index] == src2;
    
        GBV.BVSEQ.LemmaSeqSub(src1, src2, dst, carry);

        assert to_nat(src1) - to_nat(src2) + carry * pow_BASE(index) == to_nat(dst);

        GBV.BVSEQ.LemmaSeqNatBound(dst);
    }

/* end section on multi word subtraction */

/* begin section on mont loop */

    lemma mont_loop_cong_lemma(
        p1: dw_view_t,
        a0: uint,
        y0: uint,
        xi: uint,
        w25: uint,
        w26: uint,
        m0d: uint)

        requires a0 + y0 * xi == p1.full;
        requires to_nat([w25, w26]) == p1.lh * m0d;
        ensures cong_BASE(w25, (a0 + y0 * xi) * m0d);
    {
        calc ==> {
            true;
            cong_BASE(a0 + y0 * xi, p1.full);
                { dw_view_lemma(p1); }
            cong_BASE(a0 + y0 * xi, p1.lh + p1.uh * BASE());
                { LemmaAddMulModNoop(p1.lh, p1.uh, BASE()); }
            cong_BASE(a0 + y0 * xi, p1.lh);
            cong_BASE(p1.lh, a0 + y0 * xi);
                { LemmaModMulEquivalentAuto(); }
            cong_BASE(p1.lh * m0d, (a0 + y0 * xi) * m0d);
        }

        calc ==> {
            true;
                { BVSEQ.LemmaSeqLen2([w25, w26]); }
            w25 + w26 * BASE() == p1.lh * m0d;
            cong_BASE(w25 + w26 * BASE(), p1.lh * m0d);
            cong_BASE(w25 + w26 * BASE(), (a0 + y0 * xi) * m0d);
                { LemmaAddMulModNoop(w25, w26, BASE()); }
            cong_BASE(w25, (a0 + y0 * xi) * m0d);
        }
    }

    lemma mont_loop_divisible_lemma(
        ui: int,
        m0d: int,
        p1: dw_view_t,
        p2: dw_view_t,
        m0: int)

        requires p2.full == ui * m0 + p1.lh;
        requires cong_BASE(m0d * m0, -1);
        requires cong_BASE(ui, p1.full * m0d);
        ensures p2.lh == 0;
    {
        var p1_full := p1.full as int;

        assert cong_BASE(ui * m0, -p1_full) by {
            assert cong_BASE(m0d * m0 * p1.full, -p1_full) by {
                LemmaModMulEquivalent(m0d * m0, -1, p1.full, BASE());
            }
            assert cong_BASE(ui * m0, p1.full * m0d * m0) by {
                LemmaModMulEquivalentAuto();
            }
            assert p1.full * m0d * m0 == m0d * m0 * p1.full by {
                LemmaMulIsAssociativeAuto();
            }
        }

        calc ==> {
            cong_BASE(ui * m0, -p1_full);
            cong_BASE(ui * m0 + p1.lh , - p1_full + p1.lh);
                { dw_view_lemma(p1); }
            cong_BASE(ui * m0 + p1.lh, - (p1.uh as int * BASE() + p1.lh) + p1.lh);
            cong_BASE(ui * m0 + p1.lh, - (p1.uh as int * BASE()));
                { assert - (p1.uh as int * BASE())== - 1 * (p1.uh as int * BASE()); }
                { LemmaMulIsAssociativeAuto(); }
            cong_BASE(ui * m0 + p1.lh, - (p1.uh as int) * BASE());
                { LemmaMulModZero(- (p1.uh as int), BASE()); }
            cong_BASE(ui * m0 + p1.lh, 0);
        }

        calc ==> {
            p2.full == ui * m0 + p1.lh;
                { dw_view_lemma(p2); }
            p2.lh + p2.uh * BASE() == ui * m0 + p1.lh;
            cong_BASE(p2.lh + p2.uh * BASE(), ui * m0 + p1.lh);
            cong_BASE(ui * m0 + p1.lh, p2.lh + p2.uh * BASE());
                { LemmaAddMulModNoop(p2.lh, p2.uh, BASE()); }
            cong_BASE(ui * m0 + p1.lh, p2.lh);
            cong_BASE(p2.lh, 0);
        }

        assert cong_BASE(p2.lh, 0);
        LemmaSmallMod(p2.lh, BASE());
    }

    predicate mont_loop_inv(
        xi: uint,
        ui: uint,
        p1: dw_view_t,
        p2: dw_view_t,
        y: seq<uint>,
        m: seq<uint>,
        prev_a: seq<uint>,
        next_a: seq<uint>,
        j: nat)
    {
        && |m| == |next_a| == |y| == |prev_a| == NUM_WORDS
        && (1 <= j <= NUM_WORDS)
        && (xi * to_nat(y[..j]) + ui * to_nat(m[..j]) + to_nat(prev_a[..j]) 
            == 
        to_nat([0] + next_a[..j-1]) + p2.uh * pow_BASE(j) + p1.uh * pow_BASE(j))
    }

    lemma mont_loop_inv_pre_lemma(
        xi: uint,
        ui: uint,
        m0d: uint,
        p1: dw_view_t,
        p2: dw_view_t,
        y: seq<uint>,
        m: seq<uint>,
        a: seq<uint>)
        requires NUM_WORDS > 0;
        requires |m| == |a| == |y| == NUM_WORDS;
        requires p1.full == xi * y[0] + a[0];
        requires p2.full == ui * m[0] + p1.lh;
        requires cong_BASE(m0d * to_nat(m), -1);
        requires cong_BASE(ui, (a[0] + y[0] * xi) * m0d);

        ensures mont_loop_inv(xi, ui, p1, p2, y, m, a, a, 1)
    {
        assert cong_BASE(m0d * m[0], -1) by {
            GBV.BVSEQ.LemmaSeqLswModEquivalence(m);
            LemmaModMulEquivalent(to_nat(m), m[0], m0d, BASE());
            LemmaMulIsCommutativeAuto();
        }

        mont_loop_divisible_lemma(ui, m0d, p1, p2, m[0]);

        GBV.BVSEQ.LemmaSeqLen1(y[..1]);
        GBV.BVSEQ.LemmaSeqLen1(m[..1]);
        GBV.BVSEQ.LemmaSeqLen1(a[..1]);

        assert p2.full == p2.uh * BASE() by {
            dw_view_lemma(p2);
        }

        dw_view_lemma(p1);

        calc {
            xi * to_nat(y[..1]) + ui * to_nat(m[..1]) + to_nat(a[..1]);
                { reveal Pow(); }
            p2.uh * pow_BASE(1) + p1.uh * pow_BASE(1);
                {
                    reveal GBV.BVSEQ.ToNatRight();
                    assert to_nat([0]) == 0;
                }
            to_nat([0]) + p2.uh * pow_BASE(1) + p1.uh * pow_BASE(1);
                {
                    assert [0] + a[..0] == [0];
                    assert to_nat([0]) == to_nat([0] + a[..0]);
                }
            to_nat([0] + a[..0]) + p2.uh * pow_BASE(1) + p1.uh * pow_BASE(1);
        }
    }

    lemma mont_loop_inv_peri_lemma(
        xi: uint,
        ui: uint,
        p1: dw_view_t,
        p2: dw_view_t,
        next_p1: dw_view_t,
        next_p2: dw_view_t,
        y: seq<uint>,
        m: seq<uint>,
        prev_a: seq<uint>,
        a: seq<uint>,
        next_a: seq<uint>,
        j: nat)

        requires 1 <= j < NUM_WORDS; // this is in the loop itself
        requires mont_loop_inv(xi, ui, p1, p2, y, m, prev_a, a, j);
        requires a[j] == prev_a[j];
        requires |next_a| == NUM_WORDS;
        requires next_p1.full == p1.uh + y[j] * xi + a[j];
        requires next_p2.full == m[j] * ui + next_p1.lh + p2.uh;
        requires next_a == a[j-1 := next_p2.lh];
        ensures mont_loop_inv(xi, ui, next_p1, next_p2, y, m, prev_a, next_a, j+1);
    {
        var y_nat := to_nat(y[..j]);
        var y_nat' := to_nat(y[..j+1]);
        var y_j := y[j];

        var m_nat := to_nat(m[..j]);
        var m_nat' := to_nat(m[..j+1]);
        var m_j := m[j];

        var ia_nat := to_nat(prev_a[..j]);
        var ia_nat' := to_nat(prev_a[..j+1]);
        var a_j := prev_a[j];

        var ea_nat := to_nat([0] + a[..j-1]);
        var ea_nat' := to_nat([0] + next_a[..j]);

        var pow_BASE_j := pow_BASE(j);
        var pow_BASE_j' := pow_BASE(j+1);

        var p1_uh := p1.uh;
        var p2_uh := p2.uh;

        assert pow_BASE_j' == pow_BASE_j * BASE() by {
            LemmaMulIsCommutative(pow_BASE_j, BASE());
            reveal Pow();
        }

        assert xi * y_nat + ui * m_nat + ia_nat 
            == 
        ea_nat + p2_uh * pow_BASE_j +p1_uh * pow_BASE_j;

        assert p1_uh == next_p1.lh + next_p1.uh * BASE() - y_j * xi - a_j by {
            dw_view_lemma(next_p1);
        }

        assert p2_uh == next_p2.lh + next_p2.uh * BASE() - m_j * ui - next_p1.lh by {
            dw_view_lemma(next_p2);
        }

        assert ia_nat' == ia_nat + a_j * pow_BASE_j by {
            assert prev_a[..j+1][..j] == prev_a[..j];
            GBV.BVSEQ.LemmaToNatLeftEqToNatRightAuto();
            reveal GBV.BVSEQ.ToNatLeft();
        }

        assert y_nat' == y_nat + y_j * pow_BASE_j by {
            assert y[..j+1][..j] == y[..j];
            GBV.BVSEQ.LemmaToNatLeftEqToNatRightAuto();
            reveal GBV.BVSEQ.ToNatLeft();
        }

        assert m_nat' == m_nat + m_j * pow_BASE_j by {
            assert m[..j+1][..j] == m[..j];
            GBV.BVSEQ.LemmaToNatLeftEqToNatRightAuto();
            reveal GBV.BVSEQ.ToNatLeft();
        }

        assert ea_nat' == ea_nat + next_p2.lh * pow_BASE_j by {
            calc == {
                to_nat(next_a[..j]);
                    {
                        GBV.BVSEQ.LemmaSeqPrefix(next_a[..j], j - 1);
                        assert next_a[..j-1] == next_a[..j][..j-1];
                        reveal GBV.BVSEQ.ToNatRight();
                    }
                to_nat(next_a[..j-1]) + next_p2.lh * pow_BASE(j-1);
                to_nat(a[..j-1]) + next_p2.lh * pow_BASE(j-1);
            }

            assert ea_nat == to_nat([0] + a[..j-1]) == to_nat(a[..j-1]) * BASE() by {
                reveal GBV.BVSEQ.ToNatRight();
            }
            
            calc == {
                ea_nat';
                to_nat([0] + next_a[..j]);
                    { reveal GBV.BVSEQ.ToNatRight(); }
                to_nat(next_a[..j]) * BASE();
                (to_nat(a[..j-1]) + next_p2.lh * pow_BASE(j-1)) * BASE();
                    { LemmaMulIsDistributiveAddOtherWayAuto(); }
                to_nat(a[..j-1]) * BASE() + next_p2.lh * pow_BASE(j-1) * BASE();
            }

            assert pow_BASE(j-1) * BASE() == pow_BASE(j) by {
                reveal Pow();
            }

            LemmaMulIsAssociativeAuto();
        }

        assert xi * y_nat' + ui * m_nat' + ia_nat'
            ==
        ea_nat' + next_p2.uh * pow_BASE_j' + next_p1.uh * pow_BASE_j' by {
            LemmaMulProperties();
        }
    }

    lemma mont_loop_inv_post_lemma(
        xi: uint,
        ui: uint,
        p1: dw_view_t,
        p2: dw_view_t,
        y: seq<uint>,
        m: seq<uint>,
        prev_a: seq<uint>,
        a: seq<uint>,
        bout: uint1)

        requires NUM_WORDS > 0;
        requires mont_loop_inv(xi, ui, p1, p2, y, m, prev_a, a, NUM_WORDS);
        requires GBV.addc(p1.uh, p2.uh, 0) == (a[NUM_WORDS-1], bout);

        ensures to_nat(a) * BASE() + bout * pow_BASE(NUM_WORDS+1)
            == xi * to_nat(y) + ui * to_nat(m) + to_nat(prev_a);
    {
        // var m := to_nat(m);
        calc {
            to_nat(a) * BASE() + bout * pow_BASE(NUM_WORDS+1);
                {
                    GBV.BVSEQ.LemmaToNatLeftEqToNatRight(a);
                    reveal GBV.BVSEQ.ToNatLeft();
                    GBV.BVSEQ.LemmaToNatLeftEqToNatRight(a[..NUM_WORDS-1]);
                }
            (to_nat(a[..NUM_WORDS-1]) + a[NUM_WORDS-1] * pow_BASE(NUM_WORDS-1)) * BASE() + bout * pow_BASE(NUM_WORDS+1);
                { LemmaMulIsDistributiveAddOtherWayAuto(); }
            to_nat(a[..NUM_WORDS-1]) * BASE() + a[NUM_WORDS-1] * pow_BASE(NUM_WORDS-1) * BASE() + bout * pow_BASE(NUM_WORDS+1);
                {
                    reveal Pow();
                    LemmaMulIsCommutativeAuto();
                    LemmaMulIsAssociativeAuto();
                }
            to_nat(a[..NUM_WORDS-1]) * BASE() + a[NUM_WORDS-1] * pow_BASE(NUM_WORDS) + bout * BASE() * pow_BASE(NUM_WORDS);
                { LemmaMulIsDistributiveAuto(); }
            to_nat(a[..NUM_WORDS-1]) * BASE() + p2.uh * pow_BASE(NUM_WORDS) + p1.uh * pow_BASE(NUM_WORDS);
                { reveal GBV.BVSEQ.ToNatRight(); }
            to_nat([0] + a[..NUM_WORDS-1]) + p2.uh * pow_BASE(NUM_WORDS) + p1.uh * pow_BASE(NUM_WORDS);
                {
                    assert y == y[..NUM_WORDS];
                    assert m == m[..NUM_WORDS];
                    assert prev_a == prev_a[..NUM_WORDS];
                }
            xi * to_nat(y) + ui * to_nat(m) + to_nat(prev_a);
        }
    }

    lemma mont_loop_cond_sub_borrow_lemma(xi: uint,
        ui: uint,
        y: seq<uint>,
        m: nat,
        prev_a: nat,
        a: seq<uint>,
        next_a: seq<uint>,
        next_bout: uint1)

        requires m != 0;
        requires |next_a| == |y| == NUM_WORDS;
        requires prev_a < m + to_nat(y);
        requires to_nat(a) * BASE() + pow_BASE(NUM_WORDS+1)
            == xi * to_nat(y) + ui * m + prev_a;
        requires to_nat(next_a) - pow_BASE(NUM_WORDS) * next_bout == to_nat(a) - m
        requires to_nat(a) + pow_BASE(NUM_WORDS) < to_nat(y) + m

        ensures to_nat(next_a) < m + to_nat(y)
        ensures IsModEquivalent(to_nat(next_a) * BASE(), xi * to_nat(y) + ui * m + prev_a, m)
    {
        if to_nat(a) >= m {
            GBV.BVSEQ.LemmaSeqNatBound(y);
            assert to_nat(a) + pow_BASE(NUM_WORDS) < to_nat(y) + m;
            assert false; // prove by contradiction
        }
        if next_bout != 1 {
            GBV.BVSEQ.LemmaSeqNatBound(next_a);
            assert false; // prove by contradiction
        }
        
        assert next_bout == 1;

        calc {
            to_nat(next_a) * BASE();
            (to_nat(a) + pow_BASE(NUM_WORDS) * next_bout - m) * BASE();
            (to_nat(a) - m + pow_BASE(NUM_WORDS) * next_bout) * BASE();
                { LemmaMulIsDistributive(BASE(), to_nat(a) - m, pow_BASE(NUM_WORDS) * next_bout); }
            (to_nat(a) - m) * BASE() + (pow_BASE(NUM_WORDS) * next_bout) * BASE();
            (to_nat(a) - m) * BASE() + pow_BASE(NUM_WORDS) * BASE() * next_bout;
                {
                    reveal Pow();
                    LemmaMulIsCommutativeAuto();
                    assert pow_BASE(NUM_WORDS) * BASE() == pow_BASE(NUM_WORDS + 1);
                }
            (to_nat(a) - m) * BASE() + pow_BASE(NUM_WORDS+1) * next_bout;
                { LemmaMulIsDistributive(BASE(), to_nat(a), m); }
            to_nat(a) * BASE() - m * BASE() + pow_BASE(NUM_WORDS+1) * next_bout;
            xi * to_nat(y) + ui * m + prev_a - m * BASE();
        }
        
        calc ==> {
            true;
            IsModEquivalent(to_nat(next_a) * BASE(), xi * to_nat(y) + ui * m + prev_a - m * BASE(), m);
                {
                    LemmaModMultiplesVanish(-1 * BASE(), xi * to_nat(y) + ui * m + prev_a, m);
                    LemmaMulIsAssociativeAuto();
                    LemmaMulIsCommutativeAuto();
                }
            IsModEquivalent(to_nat(next_a) * BASE(), xi * to_nat(y) + ui * m + prev_a, m);
        }
    }

    lemma mont_loop_cond_sub_lemma(
        xi: uint,
        ui: uint,
        y: seq<uint>,
        m: nat,
        prev_a: nat,
        a: seq<uint>,
        next_a: seq<uint>,
        bout: uint1,
        next_bout: uint1)

        requires m != 0;
        requires |next_a| == |y| == NUM_WORDS;
        requires prev_a < m + to_nat(y);
        requires to_nat(a) * BASE() + bout * pow_BASE(NUM_WORDS+1)
            == xi * to_nat(y) + ui * m + prev_a;
        requires bout == 0 ==>
            to_nat(a) == to_nat(next_a)
        requires bout == 1 ==>
            to_nat(next_a) - pow_BASE(NUM_WORDS) * next_bout == to_nat(a) - m

        ensures to_nat(next_a) < m + to_nat(y)
        ensures IsModEquivalent(to_nat(next_a) * BASE(), xi * to_nat(y) + ui * m + prev_a, m)
    {
        if to_nat(a) + bout * pow_BASE(NUM_WORDS) >= to_nat(y) + m {
            calc {
                (to_nat(a) + bout * pow_BASE(NUM_WORDS)) * BASE();
                    { LemmaMulIsDistributiveAuto(); }
                to_nat(a) * BASE() + bout * pow_BASE(NUM_WORDS) * BASE();
                    {
                        reveal Pow();
                        LemmaMulIsAssociativeAuto();
                    }
                to_nat(a) * BASE() + bout * pow_BASE(NUM_WORDS+1);
                xi * to_nat(y) + ui * m + prev_a;
                <
                xi * to_nat(y) + ui * m + m + to_nat(y);
                    { LemmaMulIsDistributiveAuto(); }
                (xi + 1) * to_nat(y) + (ui + 1) * m;
                <=  {
                        assert xi + 1 <= BASE();
                        assert ui + 1 <= BASE();
                        LemmaMulInequalityConverseAuto();
                    }
                BASE() * to_nat(y) + BASE() * m;
                    { LemmaMulIsDistributiveAuto(); }
                (to_nat(y) + m) * BASE();
            }

            if to_nat(y) + m < to_nat(a) + bout * pow_BASE(NUM_WORDS) {
                LemmaMulStrictInequality(to_nat(y) + m, to_nat(a) + bout * pow_BASE(NUM_WORDS), BASE());
                assert false;
            }

            assert false;
        }
        
        if bout == 1 {
            mont_loop_cond_sub_borrow_lemma(xi, ui, y, m, prev_a, a, next_a, next_bout);
        }
    }

/* end section on mont loop */

/* begin section on mont mul */

    predicate montmul_inv(
        a: seq<uint>,
        x: seq<uint>,
        i: nat,
        y: seq<uint>,
        rsa: rsa_params)
    {
        && |a| == |y| == |x| == NUM_WORDS
        && i <= |x|
        && rsa_params_inv(rsa)
        && to_nat(a) < rsa.M + to_nat(y)
        && IsModEquivalent(to_nat(a) * pow_BASE(i), to_nat(x[..i]) * to_nat(y), rsa.M)
    }

    lemma montmul_inv_lemma(
        prev_a: seq<uint>,
        a: seq<uint>,
        x: seq<uint>, 
        i: nat,
        ui: int,
        y: seq<uint>, 
        rsa: rsa_params)

        requires montmul_inv(prev_a, x, i, y, rsa);
        requires |a| == NUM_WORDS;
        requires i < |x|;
        requires to_nat(a) < rsa.M + to_nat(y);
        requires IsModEquivalent(to_nat(a) * pow_BASE(1),
                x[i] * to_nat(y) + ui * rsa.M + to_nat(prev_a), rsa.M);
        ensures montmul_inv(a, x, i+1, y, rsa);
    {
        var curr_a := to_nat(a);
        var prev_a := to_nat(prev_a);
        calc ==> {
            IsModEquivalent(curr_a * pow_BASE(1), x[i] * to_nat(y) + ui * rsa.M + prev_a, rsa.M);
                {
                    LemmaMulIsCommutativeAuto();
                    LemmaModMultiplesVanish(ui, x[i] * to_nat(y) + prev_a, rsa.M);
                }
            IsModEquivalent(curr_a * pow_BASE(1), x[i] * to_nat(y) + prev_a, rsa.M);
                {
                    LemmaModMulEquivalent(curr_a * pow_BASE(1), x[i] * to_nat(y) + prev_a, pow_BASE(i), rsa.M);
                    LemmaMulIsDistributiveAuto();
                }
            IsModEquivalent(curr_a * pow_BASE(1) * pow_BASE(i), x[i] * to_nat(y) * pow_BASE(i) + prev_a * pow_BASE(i), rsa.M);
                {
                    reveal Pow();
                    LemmaMulIsAssociativeAuto();
                }
            IsModEquivalent(curr_a * pow_BASE(1+i), x[i] * to_nat(y) * pow_BASE(i) + prev_a * pow_BASE(i), rsa.M);
                {
                    LemmaAddModNoopRight(x[i] * to_nat(y) * pow_BASE(i), prev_a * pow_BASE(i), rsa.M);
                    LemmaAddModNoopRight(x[i] * to_nat(y) * pow_BASE(i), to_nat(x[..i]) * to_nat(y), rsa.M);
                }
            IsModEquivalent(curr_a * pow_BASE(1+i), x[i] * to_nat(y) * pow_BASE(i) + to_nat(x[..i]) * to_nat(y), rsa.M);
                { LemmaMulProperties(); }
            IsModEquivalent(curr_a * pow_BASE(1+i), (x[i] * pow_BASE(i) + to_nat(x[..i])) * to_nat(y), rsa.M);
                {
                    assert x[..i+1][..i] == x[..i];
                    GBV.BVSEQ.LemmaToNatLeftEqToNatRightAuto();
                    reveal GBV.BVSEQ.ToNatLeft();
                }
            IsModEquivalent(curr_a * pow_BASE(1+i), to_nat(x[..i+1]) * to_nat(y), rsa.M);
        }

        assert IsModEquivalent(curr_a * pow_BASE(1+i), to_nat(x[..i+1]) * to_nat(y), rsa.M);
    }

    lemma montmul_inv_lemma_0(
        a: seq<uint>,
        x: seq<uint>, 
        i: nat,
        y: seq<uint>, 
        rsa: rsa_params)

        requires |a| == |x| == |y| == NUM_WORDS;
        requires to_nat(a) == 0;
        requires rsa_params_inv(rsa);
        requires i == 0;
        
        ensures montmul_inv(a, x, i, y, rsa);
    {
        assert to_nat(x[..i]) == 0 by {
            reveal GBV.BVSEQ.ToNatRight();
        }
        assert montmul_inv(a, x, i, y, rsa);
    }

    lemma r_r_inv_cancel_lemma(a: nat, b: nat, rsa: rsa_params)
        requires rsa_params_inv(rsa);
        requires IsModEquivalent(a, b * rsa.R_INV * rsa.R, rsa.M);
        ensures IsModEquivalent(a, b, rsa.M);
    {
        assert IsModEquivalent(b * rsa.R_INV * rsa.R, b, rsa.M) by {
            LemmaModMulEquivalent(rsa.R_INV * rsa.R, 1, b, rsa.M);
            LemmaMulIsAssociativeAuto();
        }
    }

    lemma montmul_inv_lemma_1(
        a_view: seq<uint>,
        x: seq<uint>,
        y: seq<uint>,
        rsa: rsa_params)
    
        requires montmul_inv(a_view, x, NUM_WORDS, y, rsa);
        ensures IsModEquivalent(to_nat(a_view), to_nat(x) * to_nat(y) * rsa.R_INV, rsa.M);
    {
        var m := rsa.M;
        var a := to_nat(a_view);
        assert x[..NUM_WORDS] == x;

        calc ==> {
            IsModEquivalent(a * rsa.R, to_nat(x) * to_nat(y), m);
                { LemmaModMulEquivalentAuto(); }
            IsModEquivalent(a * rsa.R * rsa.R_INV, to_nat(x) * to_nat(y) * rsa.R_INV, m);
            IsModEquivalent(to_nat(x) * to_nat(y) * rsa.R_INV, a * rsa.R * rsa.R_INV, m);
                {
                    LemmaMulIsAssociativeAuto();
                    LemmaMulNonnegativeAuto();
                    r_r_inv_cancel_lemma(to_nat(x) * to_nat(y) * rsa.R_INV, a, rsa);
                }
            IsModEquivalent(to_nat(x) * to_nat(y) * rsa.R_INV, a, m);
            IsModEquivalent(a, to_nat(x) * to_nat(y) * rsa.R_INV, m);
        }
    }

/* end section on mont mul */

/* start section on mont mod exp */

    predicate modexp_var_inv(
        a: nat,
        sig: nat,
        i: nat,
        rsa: rsa_params)
        requires rsa.M != 0;
    {
        LemmaPowPositiveAuto();
        IsModEquivalent(a, Pow(sig, Pow(2, i)) * rsa.R, rsa.M)
    }

    lemma modexp_var_inv_pre_lemma(
        a_view: seq<uint>,
        rr: seq<uint>,
        sig: seq<uint>,
        rsa: rsa_params)

    requires montmul_inv(a_view, rr, NUM_WORDS, sig, rsa);
    requires to_nat(rr) == rsa.RR;
    ensures modexp_var_inv(to_nat(a_view), to_nat(sig), 0, rsa);
    {
        var m := rsa.M;
        var a := to_nat(a_view);
        var s := to_nat(sig);

        calc ==> {
            true;
                { LemmaModMulEquivalentAuto(); }
            IsModEquivalent(rsa.RR * rsa.R_INV, rsa.R * rsa.R * rsa.R_INV, m);
                {
                    LemmaMulProperties();
                    r_r_inv_cancel_lemma(rsa.RR * rsa.R_INV, rsa.R, rsa);
                }
            IsModEquivalent(rsa.RR * rsa.R_INV, rsa.R, m);
        }

        assert IsModEquivalent(a, s * rsa.R, m) by {
            assert IsModEquivalent(rsa.RR * rsa.R_INV * s, rsa.R * s, m) by {
                LemmaModMulEquivalentAuto();
            }
            assert IsModEquivalent(a, rsa.RR * rsa.R_INV * s, m) by {
                montmul_inv_lemma_1(a_view, rr, sig, rsa);
                LemmaMulProperties();
            }
        }
        
        reveal Pow();
    }

    lemma modexp_var_inv_peri_lemma(
        a_view: seq<uint>,
        next_a_view: seq<uint>,
        sig: nat,
        i: nat,
        rsa: rsa_params)

        requires montmul_inv(next_a_view, a_view, NUM_WORDS, a_view, rsa);
        requires sig > 0;
        requires modexp_var_inv(to_nat(a_view), sig, i, rsa);
        ensures modexp_var_inv(to_nat(next_a_view), sig, i + 1, rsa);
    {
        var m := rsa.M;
        var a := to_nat(a_view);
        var next_a := to_nat(next_a_view);

        LemmaPowPositiveAuto();
        // LemmaPowNonnegativeAuto();
        LemmaMulNonnegativeAuto();
        var next_goal := Pow(sig, Pow(2, i + 1)) * rsa.R;

        assert IsModEquivalent(a, Pow(sig, Pow(2, i)) * rsa.R, m);
        
        calc ==> {
            IsModEquivalent(a, Pow(sig, Pow(2, i)) * rsa.R, m);
                {
                    LemmaMulModNoop(a, a, m);
                    LemmaMulModNoop(Pow(sig, Pow(2, i)) * rsa.R, Pow(sig, Pow(2, i)) * rsa.R, m);
                    LemmaMulProperties();
                }
            IsModEquivalent(a * a, Pow(sig, Pow(2, i)) * rsa.R * Pow(sig, Pow(2, i)) * rsa.R, m);
                { LemmaMulIsAssociativeAuto(); }
            IsModEquivalent(a * a, Pow(sig, Pow(2, i)) * Pow(sig, Pow(2, i)) * rsa.R * rsa.R, m);
                { LemmaPowAddsAuto(); }
            IsModEquivalent(a * a, Pow(sig, Pow(2, i) + Pow(2, i)) * rsa.R * rsa.R, m);
                { reveal Pow(); }
            IsModEquivalent(a * a, next_goal * rsa.R, m);
                { LemmaModMulEquivalentAuto(); }
            IsModEquivalent(a * a * rsa.R_INV, next_goal * rsa.R * rsa.R_INV, m);
                {
                    assert IsModEquivalent(next_a, a * a * rsa.R_INV, m) by {
                        montmul_inv_lemma_1(next_a_view, a_view, a_view, rsa);
                    }
                    LemmaMulIsAssociativeAuto();
                }
            IsModEquivalent(next_a, next_goal * rsa.R_INV * rsa.R, m);
                { r_r_inv_cancel_lemma(next_a, next_goal, rsa); }
            IsModEquivalent(next_a, next_goal, m);
        }
    }

    lemma modexp_var_inv_post_lemma(
        a_view: seq<uint>,
        next_a_view: seq<uint>,
        sig: seq<uint>,
        rsa: rsa_params)

        requires montmul_inv(next_a_view, a_view, NUM_WORDS, sig, rsa);
        requires modexp_var_inv(to_nat(a_view), to_nat(sig), rsa.E0, rsa);
        ensures IsModEquivalent(to_nat(next_a_view), Pow(to_nat(sig), rsa.E), rsa.M);
    {
        var m := rsa.M;
        var a := to_nat(a_view);
        var next_a := to_nat(next_a_view);
        var s := to_nat(sig);

        LemmaPowPositiveAuto();
        // LemmaPowNonnegativeAuto();
        var cur := Pow(s, Pow(2, rsa.E0));

        assert IsModEquivalent(a, cur * rsa.R, m);

        calc ==> {
            IsModEquivalent(a, cur * rsa.R, m);
                { LemmaModMulEquivalentAuto(); }
            IsModEquivalent(a * (s * rsa.R_INV), (cur * rsa.R) * (s * rsa.R_INV), m);
                { LemmaMulIsAssociativeAuto(); }
            IsModEquivalent(a * s * rsa.R_INV, cur * rsa.R * s * rsa.R_INV, m);
                {
                    assert IsModEquivalent(next_a, a * s * rsa.R_INV, m) by {
                        montmul_inv_lemma_1(next_a_view, a_view, sig, rsa);
                    }
                }
            IsModEquivalent(next_a, cur * rsa.R * s * rsa.R_INV, m);
                {
                    LemmaMulProperties();
                    r_r_inv_cancel_lemma(next_a, cur * s, rsa);
                }
            IsModEquivalent(next_a, cur * s, m);
                {
                    LemmaMulIsCommutativeAuto();
                    reveal Pow();
                }
            IsModEquivalent(next_a, Pow(s, Pow(2, rsa.E0) + 1), m);
            IsModEquivalent(next_a, Pow(s, rsa.E), m);
            IsModEquivalent(to_nat(next_a_view), Pow(to_nat(sig), rsa.E), m);
        }
    }

    lemma modexp_var_correct_lemma(
        raw_val: nat,
        adjusted_val: nat,
        carry: bool,
        rsa: rsa_params)

    requires rsa_params_inv(rsa);
    requires raw_val < rsa.SIG + rsa.M;
    requires IsModEquivalent(raw_val, Pow(rsa.SIG, rsa.E), rsa.M);
    requires carry ==> raw_val < rsa.M;
    requires !carry ==> raw_val - rsa.M == adjusted_val;

    ensures carry ==> raw_val == Pow(rsa.SIG, rsa.E) % rsa.M;
    ensures !carry ==> adjusted_val == Pow(rsa.SIG, rsa.E) % rsa.M;
    {
        if carry {
            LemmaSmallMod(raw_val, rsa.M);
            assert raw_val == Pow(rsa.SIG, rsa.E) % rsa.M;
        } else {
            calc ==> {
                true;
                    { LemmaSubModNoopRight(raw_val, rsa.M as int, rsa.M); }
                IsModEquivalent(raw_val, adjusted_val, rsa.M);
                IsModEquivalent(adjusted_val, Pow(rsa.SIG, rsa.E), rsa.M);
            }

            LemmaSmallMod(adjusted_val, rsa.M);
        }
    }

/* end section on mont mod exp */

}

module bv256_mm_lemmas refines generic_mm_lemmas {
    import opened GBV = bv256_ops
    import opened ot_machine

    type uint512_view_t = dw_view_t

    predicate valid_uint512_view(
        wdrs: wdrs_t, num: uint512_view_t,
        li: int, ui: int)
        requires -1 <= li < BASE_5;
        requires -1 <= ui < BASE_5;
    {
        && (li == NA || wdrs[li] == num.lh)
        && (ui == NA || wdrs[ui] == num.uh)
    }

    const NUM_WORDS := 12

    const B  : int := BASE_64;
    const B2 : int := B * B;
    const B3 : int := B * B * B;
    const B4 : int := B * B * B * B;
    const B5 : int := B * B * B * B * B;
    const B6 : int := B * B * B * B * B * B;
    const B8 : int := B4 * B4;

    lemma mul256_correct_lemma(
        p0: uint256,
        p1: uint256,
        p2: uint256,
        p3: uint256,
        p4: uint256,
        p5: uint256,
        p6: uint256,
        p7: uint256,
        p8: uint256,
        p9: uint256,
        p10: uint256,
        p11: uint256,
        p12: uint256,
        p13: uint256,
        p14: uint256,
        p15: uint256,
        r0: uint256,
        r1: uint256,
        r2: uint256,
        r3: uint256,

        x: uint256,
        y: uint256,

        t0: uint256,
        t1: uint256,
        t2: uint256,
        u0: uint256,
        u1: uint256,
        u2: uint256,
        wacc: uint256)

        requires
            && p0 == otbn_qmul(x, 0, y, 0)
            && p1 == otbn_qmul(x, 1, y, 0)
            && p2 == otbn_qmul(x, 0, y, 1)
            && p3 == otbn_qmul(x, 2, y, 0)
            && p4 == otbn_qmul(x, 1, y, 1)
            && p5 == otbn_qmul(x, 0, y, 2)
            && p6 == otbn_qmul(x, 3, y, 0)
            && p7 == otbn_qmul(x, 2, y, 1)
            && p8 == otbn_qmul(x, 1, y, 2)
            && p9 == otbn_qmul(x, 0, y, 3)
            && p10 == otbn_qmul(x, 3, y, 1)
            && p11 == otbn_qmul(x, 2, y, 2)
            && p12 == otbn_qmul(x, 1, y, 3)
            && p13 == otbn_qmul(x, 3, y, 2)
            && p14 == otbn_qmul(x, 2, y, 3)
            && p15 == otbn_qmul(x, 3, y, 3)
            && r0 == p0 + (p1 + p2) * B
            && r1 == uh(r0) + p3 + p4 + p5 + (p6 + p7 + p8 + p9) * B
            && r2 == uh(r1) + p10 + p11 + p12 + (p13 + p14) * B
            && r3 == uh(r2) + p15
            && t1 == otbn_hwb(t0, lh(r0), true)
            && t2 == otbn_hwb(t1, lh(r1), false)
            && u1 == otbn_hwb(u0, lh(r2), true)
            && u2 == otbn_hwb(u1, lh(r3), false)
            && wacc == uh(r3)

        ensures
            to_nat([t2, u2]) == x * y;
    {
        assert t2 == lh(r0) + lh(r1) * B2 by {
            otbn_hwb_lemma(t0, t1, t2, lh(r0), lh(r1));
        }

        assert u2 == lh(r2) + lh(r3) * B2 by {
            otbn_hwb_lemma(u0, u1, u2, lh(r2), lh(r3));
        }

        assert x == otbn_qsel(x, 0) + otbn_qsel(x, 1) * B + otbn_qsel(x, 2) * B2 + otbn_qsel(x, 3) * B3 by {
            uint256_quarter_split_lemma(x);
        }

        assert y == otbn_qsel(y, 0) + otbn_qsel(y, 1) * B + otbn_qsel(y, 2) * B2 + otbn_qsel(y, 3) * B3 by {
            uint256_quarter_split_lemma(y);
        }

        calc {
            t2 + u2 * B4 + wacc * B8;
                { half_split_lemma(r3); }
            t2 + (lh(r2) + r3 * B2) * B4;
                { half_split_lemma(r2); }
            t2 + (r2 - uh(r2) * B2 + r3 * B2) * B4;
            t2 + r2 * B4 - uh(r2) * B2 * B4 + r3 * B2 * B4;
            lh(r0) + lh(r1) * B2 + r2 * B4 - uh(r2) * B2 * B4 + r3 * B2 * B4;
                { LemmaMulIsAssociativeAuto(); }
            lh(r0) + lh(r1) * B2 + r2 * B4 + (r3 - uh(r2)) * B6;
            lh(r0) + lh(r1) * B2 + r2 * B4 + p15 * B6;
                { half_split_lemma(r1); }
            lh(r0) + r1 * B2 + (p10 + p11 + p12) * B4 + (p13 + p14) * B5 + p15 * B6;
                { half_split_lemma(r0); }
            p0 + (p1 + p2) * B + (p3 + p4 + p5) * B2 + (p6 + p7 + p8 + p9) * B3 + (p10 + p11 + p12) * B4 + (p13 + p14) * B5 + p15 * B6;
                {
                    reveal otbn_qmul();
                    LemmaMulProperties();
                    assume false;
                }
            x * y;
        }

        assert wacc == 0 by {
            assume false;
            // single_digit_lemma_0(x, y, B4-1);
            // assert x * y <= B8;
        }

        assert to_nat([t2, u2]) == x * y by {
            GBV.BVSEQ.LemmaSeqLen2([t2, u2]);
        }
    }
}