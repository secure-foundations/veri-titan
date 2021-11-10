include "generic_bv_ops.dfy"
include "bv256_ops.dfy"

abstract module generic_mm_lemmas {
    import opened GBV: generic_bv_ops

    import opened Mul
    import opened Power
    import opened DivMod
    import integers

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

    function BASE_POW(e: nat): nat
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
        && rsa.R == BASE_POW(NUM_WORDS)
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
        c1: integers.uint1, c2: integers.uint1,
        z_lh: uint, z_uh: uint)

        requires dw_add_is_safe(x_lh, x_uh, y_lh, y_uh);
        requires (z_lh, c1) == GBV.addc(x_lh, y_lh, 0);
        requires (z_uh, c2) == GBV.addc(x_uh, y_uh, c1);
        
        ensures to_nat([z_lh, z_uh]) == to_nat([x_lh, x_uh]) + to_nat([y_lh, y_uh]);
    {
        var x_full := to_nat([x_lh, x_uh]);
        var y_full := to_nat([y_lh, y_uh]);
        var z_full := to_nat([z_lh, z_uh]);

        assert GBV.BVSEQ.SeqAdd([x_lh], [y_lh]) == ([z_lh], c1) by {
            reveal GBV.BVSEQ.SeqAdd();
            assert [] + [z_lh] == [z_lh];
        }

        assert GBV.BVSEQ.SeqAdd([x_lh, x_uh], [y_lh, y_uh]) == ([z_lh, z_uh], c2) by {
            reveal GBV.BVSEQ.SeqAdd();
            assert [z_lh] + [z_uh] == [z_lh, z_uh];
        }

        assert to_nat([z_lh, z_uh]) + c2 * Pow(GBV.BVSEQ.BASE(), 2) == x_full + to_nat([y_lh, y_uh]) by {
            GBV.BVSEQ.LemmaSeqAdd([x_lh, x_uh], [y_lh, y_uh], [z_lh, z_uh], c2);
        }

        if c2 != 0 {
            reveal Pow();
            assert false;
        }
    }

    method dw_add(x_lh: uint, x_uh: uint, y_lh: uint, y_uh: uint)
        requires dw_add_is_safe(x_lh, x_uh, y_lh, y_uh);
    {
        var (z_lh, c1) := GBV.addc(x_lh, y_lh, 0);
        var (z_uh, c2) := GBV.addc(x_uh, y_uh, c1);
        dw_add_lemma(x_lh, x_uh, y_lh, y_uh, c1, c2, z_lh, z_uh);
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
    ensures to_nat(dst) == to_nat(src1) - to_nat(src2) + carry * BASE_POW(|dst|);
    ensures carry == 0 <==> to_nat(src1) >= to_nat(src2)
    {
        var index := |dst|;
        assert dst[..index] == dst;
        assert src1[..index] == src1;
        assert src2[..index] == src2;
    
        GBV.BVSEQ.LemmaSeqSub(src1, src2, dst, carry);

        assert to_nat(src1) - to_nat(src2) + carry * BASE_POW(index) == to_nat(dst);

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

/*
    predicate mont_loop_inv(
        xi: uint256,
        ui: uint256,
        p1: dw_view_t,
        p2: dw_view_t,
        y: seq<uint256>,
        m: seq<uint256>,
        prev_a: seq<uint256>,
        next_a: seq<uint256>,
        j: nat)
    {
        && |m| == |next_a| == |y| == |prev_a| == NUM_WORDS
        && (1 <= j <= NUM_WORDS)
        && (xi * ToNat(y[..j]) + ui * ToNat(m[..j]) + ToNat(prev_a[..j]) 
            == 
        ToNat([0] + next_a[..j-1]) + p2.uh * pow_B256(j) + p1.uh * pow_B256(j))
    }

    lemma mont_loop_inv_pre_lemma(
        xi: uint256,
        ui: uint256,
        m0d: uint256,
        p1: dw_view_t,
        p2: dw_view_t,
        y: seq<uint256>,
        m: seq<uint256>,
        a: seq<uint256>)
        requires |m| == |a| == |y| == NUM_WORDS;
        requires p1.full == xi * y[0] + a[0];
        requires p2.full == ui * m[0] + p1.lh;
        requires cong_BASE(m0d * ToNat(m), -1);
        requires cong_BASE(ui, (a[0] + y[0] * xi) * m0d);

        ensures mont_loop_inv(xi, ui, p1, p2, y, m, a, a, 1)
    {
        assert cong_BASE(m0d * m[0], -1) by {
            LemmaSeqLswModEquivalence(m);
            LemmaModMulEquivalent(ToNat(m), m[0], m0d, BASE());
            LemmaMulIsCommutativeAuto();
        }

        mont_loop_divisible_lemma(ui, m0d, p1, p2, m[0]);

        LemmaSeqLen1(y[..1]);
        LemmaSeqLen1(m[..1]);
        LemmaSeqLen1(a[..1]);

        assert p2.full == p2.uh * BASE() by {
            uint512_view_lemma(p2);
        }

        uint512_view_lemma(p1);

        calc {
            xi * ToNat(y[..1]) + ui * ToNat(m[..1]) + ToNat(a[..1]);
                { reveal Pow(); }
            p2.uh * pow_B256(1) + p1.uh * pow_B256(1);
                {
                    reveal ToNatRight();
                    assert ToNat([0]) == 0;
                }
            ToNat([0]) + p2.uh * pow_B256(1) + p1.uh * pow_B256(1);
                {
                    assert [0] + a[..0] == [0];
                    assert ToNat([0]) == ToNat([0] + a[..0]);
                }
            ToNat([0] + a[..0]) + p2.uh * pow_B256(1) + p1.uh * pow_B256(1);

        }
    }

    lemma mont_loop_inv_peri_lemma(
        xi: uint256,
        ui: uint256,
        p1: dw_view_t,
        p2: dw_view_t,
        next_p1: dw_view_t,
        next_p2: dw_view_t,
        y: seq<uint256>,
        m: seq<uint256>,
        prev_a: seq<uint256>,
        a: seq<uint256>,
        next_a: seq<uint256>,
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
        var y_nat := ToNat(y[..j]);
        var y_nat' := ToNat(y[..j+1]);
        var y_j := y[j];

        var m_nat := ToNat(m[..j]);
        var m_nat' := ToNat(m[..j+1]);
        var m_j := m[j];

        var ia_nat := ToNat(prev_a[..j]);
        var ia_nat' := ToNat(prev_a[..j+1]);
        var a_j := prev_a[j];

        var ea_nat := ToNat([0] + a[..j-1]);
        var ea_nat' := ToNat([0] + next_a[..j]);

        var pow_B256_j := pow_B256(j);
        var pow_B256_j' := pow_B256(j+1);

        var p1_uh := p1.uh;
        var p2_uh := p2.uh;

        assert pow_B256_j' == pow_B256_j * BASE() by {
          reveal Pow();
        }

        assert xi * y_nat + ui * m_nat + ia_nat 
            == 
        ea_nat + p2_uh * pow_B256_j +p1_uh * pow_B256_j;

        assert p1_uh == next_p1.lh + next_p1.uh * BASE() - y_j * xi - a_j by {
            uint512_view_lemma(next_p1);
        }

        assert p2_uh == next_p2.lh + next_p2.uh * BASE() - m_j * ui - next_p1.lh by {
            uint512_view_lemma(next_p2);
        }

        assert ia_nat' == ia_nat + a_j * pow_B256_j by {
            assert prev_a[..j+1][..j] == prev_a[..j];
            LemmaToNatLeftEqToNatRightAuto();
            reveal ToNatLeft();
        }

        assert y_nat' == y_nat + y_j * pow_B256_j by {
            assert y[..j+1][..j] == y[..j];
            LemmaToNatLeftEqToNatRightAuto();
            reveal ToNatLeft();
        }

        assert m_nat' == m_nat + m_j * pow_B256_j by {
            assert m[..j+1][..j] == m[..j];
            LemmaToNatLeftEqToNatRightAuto();
            reveal ToNatLeft();
        }

        assert ea_nat' == ea_nat + next_p2.lh * pow_B256_j by {
            calc == {
                ToNat(next_a[..j]);
                    {
                        LemmaSeqPrefix(next_a[..j], j - 1);
                        assert next_a[..j-1] == next_a[..j][..j-1];
                        reveal ToNatRight();
                    }
                ToNat(next_a[..j-1]) + next_p2.lh * pow_B256(j-1);
                ToNat(a[..j-1]) + next_p2.lh * pow_B256(j-1);
            }

            assert ToNat([0] + a[..j-1]) == ToNat(a[..j-1]) * BASE() by {
                reveal ToNatRight();
            }

            assert ToNat([0] + next_a[..j]) == ToNat(next_a[..j]) * BASE() by {
                reveal ToNatRight();
            }

            assert pow_B256(j-1) * BASE() == pow_B256(j) by {
                reveal Pow();
            }

            LemmaMulIsAssociativeAuto();
        }

        assert xi * y_nat' + ui * m_nat' + ia_nat'
            ==
        ea_nat' + next_p2.uh * pow_B256_j' + next_p1.uh * pow_B256_j' by {
            LemmaMulProperties();
        }
    }

    lemma mont_loop_inv_post_lemma(
        xi: uint256,
        ui: uint256,
        p1: dw_view_t,
        p2: dw_view_t,
        y: seq<uint256>,
        m: seq<uint256>,
        prev_a: seq<uint256>,
        a: seq<uint256>,
        bout: uint1)

        requires mont_loop_inv(xi, ui, p1, p2, y, m, prev_a, a, NUM_WORDS);
        requires uint256_addc(p1.uh, p2.uh, 0) == (a[NUM_WORDS-1], bout);

        ensures ToNat(a) * BASE() + bout * pow_B256(NUM_WORDS+1)
            == xi * ToNat(y) + ui * ToNat(m) + ToNat(prev_a);
    {
        // var m := ToNat(m);
        calc {
            ToNat(a) * BASE() + bout * pow_B256(NUM_WORDS+1);
                {
                    LemmaToNatLeftEqToNatRight(a);
                    reveal ToNatLeft();
                    LemmaToNatLeftEqToNatRight(a[..NUM_WORDS-1]);
                }
            (ToNat(a[..NUM_WORDS-1]) + a[NUM_WORDS-1] * pow_B256(NUM_WORDS-1)) * BASE() + bout * pow_B256(NUM_WORDS+1);
            ToNat(a[..NUM_WORDS-1]) * BASE() + a[NUM_WORDS-1] * pow_B256(NUM_WORDS-1) * BASE() + bout * pow_B256(NUM_WORDS+1);
                {
                    reveal Pow();
                    LemmaMulIsCommutativeAuto();
                    LemmaMulIsAssociativeAuto();
                }
            ToNat(a[..NUM_WORDS-1]) * BASE() + a[NUM_WORDS-1] * pow_B256(NUM_WORDS) + bout * BASE() * pow_B256(NUM_WORDS);
                { LemmaMulIsDistributiveAuto(); }
            ToNat(a[..NUM_WORDS-1]) * BASE() + p2.uh * pow_B256(NUM_WORDS) + p1.uh * pow_B256(NUM_WORDS);
                { reveal ToNatRight(); }
            ToNat([0] + a[..NUM_WORDS-1]) + p2.uh * pow_B256(NUM_WORDS) + p1.uh * pow_B256(NUM_WORDS);
                {
                    assert y == y[..NUM_WORDS];
                    assert m == m[..NUM_WORDS];
                    assert prev_a == prev_a[..NUM_WORDS];
                }
            xi * ToNat(y) + ui * ToNat(m) + ToNat(prev_a);
        }
    }

    lemma mont_loop_cond_sub_borrow_lemma(xi: uint256,
        ui: uint256,
        y: seq<uint256>,
        m: nat,
        prev_a: nat,
        a: seq<uint256>,
        next_a: seq<uint256>,
        next_bout: uint1)

        requires m != 0;
        requires |next_a| == |y| == NUM_WORDS;
        requires prev_a < m + ToNat(y);
        requires ToNat(a) * BASE() + pow_B256(NUM_WORDS+1)
            == xi * ToNat(y) + ui * m + prev_a;
        requires ToNat(next_a) - pow_B256(NUM_WORDS) * next_bout == ToNat(a) - m
        requires ToNat(a) + pow_B256(NUM_WORDS) < ToNat(y) + m

        ensures ToNat(next_a) < m + ToNat(y)
        ensures IsModEquivalent(ToNat(next_a) * BASE(), xi * ToNat(y) + ui * m + prev_a, m)
    {
        if ToNat(a) >= m {
            LemmaSeqNatBound(y);
            assert ToNat(a) + pow_B256(NUM_WORDS) < ToNat(y) + m;
            assert false; // prove by contradiction
        }
        if next_bout != 1 {
            LemmaSeqNatBound(next_a);
            assert false; // prove by contradiction
        }
        
        assert next_bout == 1;

        calc {
            ToNat(next_a) * BASE();
            ToNat(a) * BASE() + pow_B256(NUM_WORDS) * BASE() - m * BASE();
                { reveal Pow(); }
            ToNat(a) * BASE() + pow_B256(NUM_WORDS+1) - m * BASE();
            xi * ToNat(y) + ui * m + prev_a - m * BASE();
        }
        
        calc ==> {
            true;
            IsModEquivalent(ToNat(next_a) * BASE(), xi * ToNat(y) + ui * m + prev_a - m * BASE(), m);
                { LemmaModMultiplesVanish(-1 * BASE(), xi * ToNat(y) + ui * m + prev_a, m); }
            IsModEquivalent(ToNat(next_a) * BASE(), xi * ToNat(y) + ui * m + prev_a, m);
        }
    }

    lemma mont_loop_cond_sub_lemma(
        xi: uint256,
        ui: uint256,
        y: seq<uint256>,
        m: nat,
        prev_a: nat,
        a: seq<uint256>,
        next_a: seq<uint256>,
        bout: uint1,
        next_bout: uint1)

        requires m != 0;
        requires |next_a| == |y| == NUM_WORDS;
        requires prev_a < m + ToNat(y);
        requires ToNat(a) * BASE() + bout * pow_B256(NUM_WORDS+1)
            == xi * ToNat(y) + ui * m + prev_a;
        requires bout == 0 ==>
            ToNat(a) == ToNat(next_a)
        requires bout == 1 ==>
            ToNat(next_a) - pow_B256(NUM_WORDS) * next_bout == ToNat(a) - m

        ensures ToNat(next_a) < m + ToNat(y)
        ensures IsModEquivalent(ToNat(next_a) * BASE(), xi * ToNat(y) + ui * m + prev_a, m)
    {
        assert ToNat(a) + bout * pow_B256(NUM_WORDS) < ToNat(y) + m by {
            calc {
                (ToNat(a) + bout * pow_B256(NUM_WORDS)) * BASE();
                ToNat(a) * BASE() + bout * pow_B256(NUM_WORDS) * BASE();
                    { reveal Pow(); }
                ToNat(a) * BASE() + bout * pow_B256(NUM_WORDS+1);
                xi * ToNat(y) + ui * m + prev_a;
                <
                xi * ToNat(y) + ui * m + m + ToNat(y);
                    { LemmaMulIsDistributiveAuto(); }
                (xi + 1) * ToNat(y) + (ui + 1) * m;
                <=  {
                        assert xi + 1 <= BASE();
                        assert ui + 1 <= BASE();
                        LemmaMulInequalityConverseAuto();
                    }
                BASE() * ToNat(y) + BASE() * m;
                (ToNat(y) + m) * BASE();
            }
        }
        
        if bout == 1 {
            mont_loop_cond_sub_borrow_lemma(xi, ui, y, m, prev_a, a, next_a, next_bout);
        }
    }

    predicate montmul_inv(
        a: seq<uint256>,
        x: seq<uint256>,
        i: nat,
        y: seq<uint256>,
        rsa: rsa_params)
    {
        && |a| == |y| == |x| == NUM_WORDS
        && i <= |x|
        && rsa_params_inv(rsa)
        && ToNat(a) < rsa.M + ToNat(y)
        && IsModEquivalent(ToNat(a) * pow_B256(i), ToNat(x[..i]) * ToNat(y), rsa.M)
    }

    lemma montmul_inv_lemma(
        prev_a: seq<uint256>,
        a: seq<uint256>,
        x: seq<uint256>, 
        i: nat,
        ui: int,
        y: seq<uint256>, 
        rsa: rsa_params)

        requires montmul_inv(prev_a, x, i, y, rsa);
        requires |a| == NUM_WORDS;
        requires i < |x|;
        requires ToNat(a) < rsa.M + ToNat(y);
        requires IsModEquivalent(ToNat(a) * pow_B256(1),
                x[i] * ToNat(y) + ui * rsa.M + ToNat(prev_a), rsa.M);
        ensures montmul_inv(a, x, i+1, y, rsa);
    {
        var curr_a := ToNat(a);
        var prev_a := ToNat(prev_a);
        calc ==> {
            IsModEquivalent(curr_a * pow_B256(1), x[i] * ToNat(y) + ui * rsa.M + prev_a, rsa.M);
                {
                    LemmaMulIsCommutativeAuto();
                    LemmaModMultiplesVanish(ui, x[i] * ToNat(y) + prev_a, rsa.M);
                }
            IsModEquivalent(curr_a * pow_B256(1), x[i] * ToNat(y) + prev_a, rsa.M);
                {
                    LemmaModMulEquivalent(curr_a * pow_B256(1), x[i] * ToNat(y) + prev_a, pow_B256(i), rsa.M);
                    LemmaMulIsDistributiveAuto();
                }
            IsModEquivalent(curr_a * pow_B256(1) * pow_B256(i), x[i] * ToNat(y) * pow_B256(i) + prev_a * pow_B256(i), rsa.M);
                {
                    reveal Pow();
                    LemmaMulIsAssociativeAuto();
                }
            IsModEquivalent(curr_a * pow_B256(1+i), x[i] * ToNat(y) * pow_B256(i) + prev_a * pow_B256(i), rsa.M);
                {
                    LemmaAddModNoopRight(x[i] * ToNat(y) * pow_B256(i), prev_a * pow_B256(i), rsa.M);
                    LemmaAddModNoopRight(x[i] * ToNat(y) * pow_B256(i), ToNat(x[..i]) * ToNat(y), rsa.M);
                }
            IsModEquivalent(curr_a * pow_B256(1+i), x[i] * ToNat(y) * pow_B256(i) + ToNat(x[..i]) * ToNat(y), rsa.M);
                { LemmaMulProperties(); }
            IsModEquivalent(curr_a * pow_B256(1+i), (x[i] * pow_B256(i) + ToNat(x[..i])) * ToNat(y), rsa.M);
                {
                    assert x[..i+1][..i] == x[..i];
                    LemmaToNatLeftEqToNatRightAuto();
                    reveal ToNatLeft();
                }
            IsModEquivalent(curr_a * pow_B256(1+i), ToNat(x[..i+1]) * ToNat(y), rsa.M);
        }

        assert IsModEquivalent(curr_a * pow_B256(1+i), ToNat(x[..i+1]) * ToNat(y), rsa.M);
    }
    */

/* end section on mont loop */

}

module bv256_mm_lemmas refines generic_mm_lemmas {
    import opened GBV = bv256_ops

    const NUM_WORDS := 12
}