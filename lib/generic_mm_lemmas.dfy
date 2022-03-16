include "generic_bv_ops.dfy"

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
        ensures IsModEquivalent(num.full, num.lh, BASE());
    {
        reveal dw_lh();
        reveal dw_uh();
        LemmaFundamentalDivMod(num.full, BASE());
        GBV.BVSEQ.LemmaSeqLen2([num.lh, num.uh]);
        assert num.full - num.lh == num.uh * BASE();
        DivMod.LemmaModMultiplesBasicAuto();
        assert (num.uh * BASE()) % BASE() == 0;
    }

    predicate dw_add_is_safe(
        x_lh: uint, x_uh: uint,
        y_lh: uint, y_uh: uint)
    {
        to_nat([x_lh, x_uh]) + to_nat([y_lh, y_uh]) < DW_BASE()
    }

    function add_carry_bit(x: uint, y: uint): uint1
    {
        if x + y >= BASE() then 1 else 0
    }

    lemma dw_add_lemma(
        x_lh: uint, x_uh: uint,
        y_lh: uint, y_uh: uint,
        carry: uint1)
    returns (z: dw_view_t)
        requires dw_add_is_safe(x_lh, x_uh, y_lh, y_uh);
        requires carry == add_carry_bit(x_lh, y_lh);
        ensures (z.lh, carry) == GBV.addc(x_lh, y_lh, 0);
        ensures (z.uh, 0) == GBV.addc(x_uh, y_uh, carry);
        ensures z.full == to_nat([x_lh, x_uh]) + to_nat([y_lh, y_uh]);
        ensures y_uh == 0 ==> z.full == to_nat([x_lh, x_uh]) + y_lh;
    {
        var (z_lh, c1) := GBV.addc(x_lh, y_lh, 0);
        var (z_uh, c2) := GBV.addc(x_uh, y_uh, c1);
        assert c1 == carry;

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

        if y_uh == 0 {
            GBV.BVSEQ.LemmaSeqLen2([y_lh, y_uh]);
            LemmaMulBasicsAuto();
            assert to_nat([y_lh, y_uh]) == y_lh;
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
        // assert (z.lh, c1) == GBV.addc(x_lh, y_lh, 0);
    }

    lemma mul_add_lemma(
        xs: seq<uint>, ys: seq<uint>, 
        carry: uint1, a: uint, b: uint)
    returns (z: dw_view_t)
        requires |xs| == |ys| == 2;
        requires to_nat(xs) == a * b;
        requires ys[1] == 0;
        requires carry == add_carry_bit(xs[0], ys[0]);
        ensures (z.lh, carry) == GBV.addc(xs[0], ys[0], 0);
        ensures (z.uh, 0) == GBV.addc(xs[1], ys[1], carry);
        ensures z.full == to_nat(xs) + ys[0];
        ensures dw_add_is_safe(xs[0], xs[1], ys[0], ys[1]);
    {
        assert xs == [xs[0], xs[1]];
        mul_add_bound_lemma(a, b, ys[0]);
        var y_val := to_nat([ys[0], ys[1]]);
        assert y_val == ys[0] by {
            GBV.BVSEQ.LemmaSeqLen2([ys[0], ys[1]]);
            assert y_val == ys[0] + 0 * BASE();
        }
        assert to_nat([xs[0], xs[1]]) + y_val < DW_BASE();
        z := dw_add_lemma(xs[0], xs[1], ys[0], ys[1], carry);
    }

    lemma mul_double_add_lemma(
        xs: seq<uint>, ys: seq<uint>, carry: uint1, a: uint, b: uint, c: uint)
    returns (z: dw_view_t)
        requires |xs| == |ys| == 2;
        requires to_nat(xs) == a * b + c;
        requires ys[1] == 0;
        requires carry == add_carry_bit(xs[0], ys[0]);
        ensures (z.lh, carry) == GBV.addc(xs[0], ys[0], 0);
        ensures (z.uh, 0) == GBV.addc(xs[1], ys[1], carry);
        ensures z.full == to_nat(xs) + ys[0];
    {
        mul_double_add_bound_lemma(a, b, c, ys[0]);
        assert xs == [xs[0], xs[1]];
        var y_val := to_nat([ys[0], ys[1]]);
        assert y_val == ys[0] by {
            GBV.BVSEQ.LemmaSeqLen2([ys[0], ys[1]]);
            assert y_val == ys[0] + 0 * BASE();
        }
        assert to_nat([xs[0], xs[1]]) +y_val < DW_BASE();
        z := dw_add_lemma(xs[0], xs[1], ys[0], ys[1], carry);
    }

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
    ensures carry * pow_BASE(|dst|) == pow_BASE(|dst|) * carry;
    ensures carry == 0 <==> to_nat(src1) >= to_nat(src2)
    {
        var index := |dst|;
        assert dst[..index] == dst;
        assert src1[..index] == src1;
        assert src2[..index] == src2;
    
        GBV.BVSEQ.LemmaSeqSub(src1, src2, dst, carry);

        assert to_nat(src1) - to_nat(src2) + carry * pow_BASE(index) == to_nat(dst);

        GBV.BVSEQ.LemmaSeqNatBound(dst);
        Mul.LemmaMulIsCommutativeAuto();
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
        requires to_nat([w25, w26]) == p1.lh * m0d;
        ensures w25 == mul(p1.lh, m0d); 
    {
        calc == {
            mul(p1.lh, m0d);
            {
                full_mul_bound_lemma(p1.lh, m0d);
                reveal dw_lh();
            }
            (p1.lh * m0d) % BASE();
            to_nat([w25, w26]) % BASE();
                { BVSEQ.LemmaSeqLen2([w25, w26]); }
            (w25 + w26 * BASE()) % BASE();
                { LemmaMulIsCommutativeAuto(); }
            (w25 + BASE() * w26) % BASE();
                { LemmaModMultiplesVanish(w26, w25, BASE()); }
            w25 % BASE();
                { LemmaSmallMod(w25, BASE()); }
            w25;
        }
    }

    lemma mont_loop_divisible_lemma(
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
        requires ui == mul(p1.lh, m0d);
        ensures p2.lh == 0;
    {
        dw_view_lemma(p1);
        dw_view_lemma(p2);

        gbassert IsModEquivalent(p2.lh, 0, BASE()) by {
            assert p2.full == ui * m[0] + p1.lh;
            assert p1.full == xi * y[0] + a[0];
            assert IsModEquivalent(p1.full, p1.lh, BASE());
            assert IsModEquivalent(p2.full, p2.lh, BASE());
            assert IsModEquivalent(to_nat(m), m[0], BASE()) by {
                GBV.BVSEQ.LemmaSeqLswModEquivalence(m);
            }
            assert IsModEquivalent(m0d * to_nat(m), -1, BASE());
            assert IsModEquivalent(ui, p1.lh * m0d, BASE()) by {
                reveal dw_lh();
                LemmaModBasicsAuto();
            }
        }
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
        && prev_a[j..] == next_a[j..]
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
        requires ui == mul(p1.lh, m0d); 
        ensures mont_loop_inv(xi, ui, p1, p2, y, m, a, a, 1)
    {
        mont_loop_divisible_lemma(xi, ui, m0d, p1, p2, y, m, a);

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
            p2.uh * BASE() + p1.uh * BASE();
                {
                    reveal GBV.BVSEQ.ToNatRight();
                    assert to_nat([0]) == 0;
                }
            to_nat([0]) + p2.uh * BASE() + p1.uh * BASE();
                {
                    assert [0] + a[..0] == [0];
                    assert to_nat([0]) == to_nat([0] + a[..0]);
                }
            to_nat([0] + a[..0]) + p2.uh * BASE() + p1.uh * BASE();
        }

        assert pow_BASE(1) == BASE() by {
            reveal Pow();
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
        requires next_p1.full == y[j] * xi + p1.uh + a[j];
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

        gbassert IsModEquivalent(to_nat(next_a) * BASE(), xi * to_nat(y) + ui * m + prev_a, m) by {
            assert pow_BASE(NUM_WORDS) * BASE() == pow_BASE(NUM_WORDS + 1) by {
                reveal Pow();
                LemmaMulIsCommutativeAuto();
            }
            assert to_nat(next_a) - pow_BASE(NUM_WORDS) == to_nat(a) - m;
            assert to_nat(a) * BASE() + pow_BASE(NUM_WORDS+1)
                == xi * to_nat(y) + ui * m + prev_a;
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
        requires IsModEquivalent(to_nat(a) * BASE(),
                x[i] * to_nat(y) + ui * rsa.M + to_nat(prev_a), rsa.M);
        ensures montmul_inv(a, x, i+1, y, rsa);
    {
        var curr_a := to_nat(a);
        var prev_a := to_nat(prev_a);

        gbassert IsModEquivalent(curr_a * pow_BASE(i+1), to_nat(x[..i+1]) * to_nat(y), rsa.M) by {
            assert IsModEquivalent(curr_a * BASE(), x[i] * to_nat(y) + ui * rsa.M + prev_a, rsa.M);
            assert IsModEquivalent(prev_a * pow_BASE(i), to_nat(x[..i]) * to_nat(y), rsa.M);
            assert BASE() * pow_BASE(i) == pow_BASE(i+1) by {
                reveal Pow();
                LemmaMulIsAssociativeAuto();
            }
            assert to_nat(x[..i+1]) == to_nat(x[..i]) + x[i] * pow_BASE(i) by {
                assert x[..i+1][..i] == x[..i];
                GBV.BVSEQ.LemmaToNatLeftEqToNatRightAuto();
                reveal GBV.BVSEQ.ToNatLeft();
            }
        }
    }

    lemma montmul_inv_lemma_0(
        a: seq<uint>,
        x: seq<uint>, 
        y: seq<uint>, 
        rsa: rsa_params)

        requires |a| == |x| == |y| == NUM_WORDS;
        requires a == GBV.BVSEQ.SeqZero(NUM_WORDS);
        requires rsa_params_inv(rsa);
        
        ensures montmul_inv(a, x, 0, y, rsa);
    {
        assert to_nat(x[..0]) == 0 by {
            reveal GBV.BVSEQ.ToNatRight();
        }
        assert montmul_inv(a, x, 0, y, rsa);
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

        gbassert IsModEquivalent(a, to_nat(x) * to_nat(y) * rsa.R_INV, m) by {
            assert IsModEquivalent(a * rsa.R, to_nat(x) * to_nat(y), m);
            assert IsModEquivalent(rsa.R_INV * rsa.R, 1, m);
        }
    }

/* end section on mont mul */

/* start section on mont mod exp */

    predicate modexp_var_inv(
        a: nat,
        i: nat,
        rsa: rsa_params)
    {
        LemmaPowPositiveAuto();
        && rsa_params_inv(rsa)
        && IsModEquivalent(a, Pow(rsa.SIG, Pow(2, i)) * rsa.R, rsa.M)
    }

    lemma modexp_var_inv_pre_lemma(
        a_view: seq<uint>,
        rr: seq<uint>,
        sig: seq<uint>,
        rsa: rsa_params)

    requires montmul_inv(a_view, rr, NUM_WORDS, sig, rsa);
    requires to_nat(sig) == rsa.SIG;
    requires to_nat(rr) == rsa.RR;
    ensures modexp_var_inv(to_nat(a_view), 0, rsa);
    {
        var m := rsa.M;
        var a := to_nat(a_view);
        var s := to_nat(sig);

        assert rr[..NUM_WORDS] == rr;

        gbassert IsModEquivalent(a, s * rsa.R, rsa.M) by {
            assert IsModEquivalent(a * rsa.R, rsa.RR * s, rsa.M);
            assert IsModEquivalent(rsa.R_INV * rsa.R, 1, rsa.M);
            assert IsModEquivalent(rsa.RR, rsa.R * rsa.R, rsa.M);
        }
        reveal Pow();
    }

    lemma modexp_var_inv_peri_lemma(
        a_view: seq<uint>,
        next_a_view: seq<uint>,
        i: nat,
        rsa: rsa_params)

        requires montmul_inv(next_a_view, a_view, NUM_WORDS, a_view, rsa);
        requires modexp_var_inv(to_nat(a_view), i, rsa);
        ensures modexp_var_inv(to_nat(next_a_view), i + 1, rsa);
    {
        var a := to_nat(a_view);
        var next_a := to_nat(next_a_view);
        var sig := rsa.SIG;
        assert a_view[..NUM_WORDS] == a_view;
    
        LemmaPowPositiveAuto();
        LemmaMulNonnegativeAuto();
        var next_goal := Pow(sig, Pow(2, i + 1)) * rsa.R;
        var exp := Pow(sig, Pow(2, i));

        gbassert IsModEquivalent(next_a, exp * exp * rsa.R, rsa.M) by {
            assert IsModEquivalent(rsa.R_INV * rsa.R, 1, rsa.M);
            assert IsModEquivalent(a, exp * rsa.R, rsa.M);
            assert IsModEquivalent(next_a * rsa.R, a * a, rsa.M);
        }

        assert next_goal == exp * exp * rsa.R by {
            LemmaPowAdds(sig,  Pow(2, i), Pow(2, i));
            assert exp * exp == Pow(sig, Pow(2, i) * 2);
            reveal Pow();
        }
    }

    lemma modexp_var_inv_post_lemma(
        a_view: seq<uint>,
        next_a_view: seq<uint>,
        sig: seq<uint>,
        rsa: rsa_params)

        requires montmul_inv(next_a_view, a_view, NUM_WORDS, sig, rsa);
        requires to_nat(sig) == rsa.SIG;
        requires modexp_var_inv(to_nat(a_view), rsa.E0, rsa);
        ensures IsModEquivalent(to_nat(next_a_view), Pow(rsa.SIG, rsa.E), rsa.M);
    {
        var m := rsa.M;
        var a := to_nat(a_view);
        var next_a := to_nat(next_a_view);
        var s := to_nat(sig);

        LemmaPowPositiveAuto();
        var cur := Pow(s, Pow(2, rsa.E0));

        Mul.LemmaMulNonnegative(a, s);
        assert a * s >= 0;

        gbassert IsModEquivalent(next_a, cur * s, m) by {
            assert IsModEquivalent(a, cur * rsa.R, m);
            assert IsModEquivalent(next_a * rsa.R, a * s, m) by {
                assert a_view == a_view[..NUM_WORDS];
            }
            assert IsModEquivalent(rsa.R_INV * rsa.R, 1, m);
        }

        assert IsModEquivalent(next_a, Pow(s, Pow(2, rsa.E0) + 1), m) by {
            LemmaMulIsCommutativeAuto();
            reveal Pow();
        }

        assert IsModEquivalent(to_nat(next_a_view), Pow(to_nat(sig), rsa.E), m);
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
