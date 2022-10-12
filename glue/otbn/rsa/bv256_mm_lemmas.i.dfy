include "../../../spec/arch/otbn/machine.s.dfy"
include "../../../spec/bvop/bv256_op.s.dfy"
include "../../../spec/arch/otbn/vale.i.dfy"
include "../../generic_mm_lemmas.dfy"

module bv256_mm_lemmas refines generic_mm_lemmas {
    import opened GBV = bv256_op_s
    import bv32_op_s
    import opened ot_machine
    import opened ot_vale
    import opened ot_abstraction
    import opened mem

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

    datatype mvars = mvars(
        x_it: iter_t,
        y_it: iter_t,

        m_it: iter_t,
        m0d_it: iter_t,
        rr_it: iter_t,
        sig_it: iter_t,
        rsa: rsa_params)

    predicate mvars_iter_init(iter: iter_t, heap: heap_t, address: int, value: int)
    {
        && (address >= 0 ==> iter_inv(iter, heap, address))
        && (value >= 0 ==> to_nat(iter.buff) == value)
        && iter.index == 0
        && |iter.buff| == NUM_WORDS
    }

    predicate m0d_it_inv(iter: iter_t, heap: heap_t, address: int)
    {
        && (address >= 0 ==> iter_inv(iter, heap, address))
        && iter.index == 0
        && |iter.buff| == 1
    }

    predicate mvars_inv(
        vars: mvars,
        heap: heap_t,
        x_ptr: int,
        y_ptr: int,
        m_ptr: int,
        m0d_ptr: int,
        rr_ptr: int,
        sig_ptr: int)
    {
        && rsa_params_inv(vars.rsa)

        && mvars_iter_init(vars.x_it, heap, x_ptr, NA)
        && mvars_iter_init(vars.y_it, heap, y_ptr, NA)
        && mvars_iter_init(vars.sig_it, heap, sig_ptr, vars.rsa.SIG)
        && mvars_iter_init(vars.m_it, heap, m_ptr, vars.rsa.M)
        && mvars_iter_init(vars.rr_it, heap, rr_ptr, vars.rsa.RR)

        && m0d_it_inv(vars.m0d_it, heap, m0d_ptr)
        && vars.m0d_it.buff[0] == vars.rsa.M0D
    }

    predicate mvars_init(
        vars: mvars,
        heap: heap_t,
        m_ptr: uint32,
        m0d_ptr: uint32,
        rr_ptr: uint32,
        sig_ptr: uint32,
        out_ptr: uint32)
    {
        && rsa_params_inv(vars.rsa)
        && vars.rsa.E0 < BASE_32
        && is_xword_pointee(heap, 0, vars.rsa.E0)
        && is_xword_pointee(heap, 4, NUM_WORDS)
        && is_xword_pointee(heap, 16, m_ptr)
        && is_xword_pointee(heap, 8, m0d_ptr)
        && is_xword_pointee(heap, 12, rr_ptr)
        && is_xword_pointee(heap, 20, sig_ptr)
        && is_xword_pointee(heap, 28, out_ptr)

        && mvars_inv(vars, heap, NA, NA, m_ptr, m0d_ptr, rr_ptr, sig_ptr)
        && heap_b256_ptr_valid(heap, out_ptr)
        && |heap[out_ptr].b256| == NUM_WORDS

        && out_ptr != m0d_ptr
        && out_ptr != rr_ptr
        && out_ptr != m_ptr
        && out_ptr != sig_ptr
    }

    function method half_mul_256(a: uint256, b: uint256): uint256
    {
        mul(a, b)
    }

    lemma mul256_correct_lemma(
        p0: uint256, p1: uint256, p2: uint256, p3: uint256,
        p4: uint256, p5: uint256, p6: uint256, p7: uint256,
        p8: uint256, p9: uint256, p10: uint256, p11: uint256,
        p12: uint256, p13: uint256, p14: uint256, p15: uint256,
        r0: uint256, r1: uint256, r2: uint256, r3: uint256,
        x: uint256, y: uint256,
        t0: uint256, t1: uint256, t2: uint256,
        u0: uint256, u1: uint256, u2: uint256,
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
            && r0 == p0 + (p1 + p2) * integers.BASE_64
            && r1 == uh(r0) + p3 + p4 + p5 + (p6 + p7 + p8 + p9) * integers.BASE_64
            && r2 == uh(r1) + p10 + p11 + p12 + (p13 + p14) * integers.BASE_64
            && r3 == uh(r2) + p15
            && t1 == otbn_hwb(t0, lh(r0), true)
            && t2 == otbn_hwb(t1, lh(r1), false)
            && u1 == otbn_hwb(u0, lh(r2), true)
            && u2 == otbn_hwb(u1, lh(r3), false)
            && wacc == uh(r3)

        ensures
            to_nat([t2, u2]) == x * y;
    {
        var x_0, x_1, x_2, x_3  := otbn_qsel(x, 0), otbn_qsel(x, 1), otbn_qsel(x, 2), otbn_qsel(x, 3);
        var y_0, y_1, y_2, y_3  := otbn_qsel(y, 0), otbn_qsel(y, 1), otbn_qsel(y, 2), otbn_qsel(y, 3);
        var B :int := integers.BASE_64;

        gbassert t2 + u2*B*B*B*B + wacc*B*B*B*B*B*B*B*B
            ==
            p0 + (p1 + p2)*B + (p3 + p4 + p5)*B*B + (p6 + p7 + p8 + p9)*B*B*B + (p10 + p11 + p12)*B*B*B*B + (p13 + p14)*B*B*B*B*B + p15*B*B*B*B*B*B
        by {
            assert r0 == p0 + (p1 + p2)*B;
            assert r1 == uh(r0) + p3 + p4 + p5 + (p6 + p7 + p8 + p9)*B;
            assert r2 == uh(r1) + p10 + p11 + p12 + (p13 + p14)*B;
            assert r3 == uh(r2) + p15;
            assert r0 == lh(r0) + uh(r0)*B*B by {
                half_split_lemma(r0);
            }
            assert r1 == lh(r1) + uh(r1)*B*B by {
                half_split_lemma(r1);
            }
            assert r2 == lh(r2) + uh(r2)*B*B by {
                half_split_lemma(r2);
            }
            assert r3 == lh(r3) + uh(r3)*B*B by {
                half_split_lemma(r3);
            }
            assert wacc == uh(r3);
            assert t2 == lh(r0) + lh(r1)*B*B  by {
                otbn_hwb_lemma(t0, t1, t2, lh(r0), lh(r1));
            }
            assert u2 == lh(r2) + lh(r3)*B*B  by {
                otbn_hwb_lemma(u0, u1, u2, lh(r2), lh(r3));
            }
        }

        reveal otbn_qmul();

        gbassert p0 + (p1 + p2)*B + (p3 + p4 + p5)*B*B + (p6 + p7 + p8 + p9)*B*B*B + (p10 + p11 + p12)*B*B*B*B + (p13 + p14)*B*B*B*B*B + p15*B*B*B*B*B*B
            ==
            x * y
        by {
            assert x == x_0 + x_1*B + x_2*B*B + x_3*B*B*B by {
                uint256_quarter_split_lemma(x);
            }
            assert y == y_0 + y_1*B + y_2*B*B + y_3*B*B*B by {
                uint256_quarter_split_lemma(y);
            }
            assert p0 == x_0 * y_0;
            assert p1 == x_1 * y_0;
            assert p2 == x_0 * y_1;
            assert p3 == x_2 * y_0;
            assert p4 == x_1 * y_1;
            assert p5 == x_0 * y_2;
            assert p6 == x_3 * y_0;
            assert p7 == x_2 * y_1;
            assert p8 == x_1 * y_2;
            assert p9 == x_0 * y_3;
            assert p10 == x_3 * y_1;
            assert p11 == x_2 * y_2;
            assert p12 == x_1 * y_3;
            assert p13 == x_3 * y_2;
            assert p14 == x_2 * y_3;
            assert p15 == x_3 * y_3;
        }

        assert t2 + u2*B*B*B*B + wacc*B*B*B*B*B*B*B*B == x * y;

        var B4 := B*B*B*B;
        var B8 := B4 * B4;

        assert wacc == 0 by {
            assert x * y <= (B4 - 1) * (B4 - 1) by {
                Mul.LemmaMulUpperBound(x, B4 - 1, y, B4 - 1);
            }
            assert x * y <= B8;
        }

        assert to_nat([t2, u2]) == x * y by {
            GBV.BVSEQ.LemmaSeqLen2([t2, u2]);
        }
    }

    lemma and_lsb_lemma(x: uint32)
        ensures x % 2 == 1 ==> bv32_op_s.and(x, 1) == 1
        ensures x % 2 == 0 ==> bv32_op_s.and(x, 1) == 0
    {
        reveal bv32_op_s.and();
    }

    lemma xor_negation_lemma(
        x: uint32)
        ensures x == 0 ==> bv32_op_s.xor(x, 1) == 1;
        ensures x == 1 ==> bv32_op_s.xor(x,1) == 0;
    {
        reveal bv32_op_s.xor();
        assert bv32_op_s.xor(0, 1) == 1;
        assert bv32_op_s.xor(1,1) == 0;
    }

    lemma read_carry_flag_lemma(flags: flags_t)
        ensures uint32_andi(flags_as_uint(flags), 1)
            == if flags.cf then 1 else 0;
    {
        var value := flags_as_uint(flags);
        assert flags.cf ==> value % 2 == 1;
        assert !flags.cf ==> value % 2 == 0;
        var carry := uint32_andi(value, 1);
        and_lsb_lemma(value);
        assert carry == if flags.cf then 1 else 0;
    }

    lemma double_modulo_selector_lemma(
        carry: uint1,
        borrow: uint1,
        select: uint32)
        requires select == bv32_op_s.and(bv32_op_s.xor(carry, 1), borrow);
        ensures select == 0 ==> (carry == 1 || borrow == 0);
        ensures select != 0 ==> (carry == 0 && borrow == 1);
    {
        reveal bv32_op_s.xor();
        reveal bv32_op_s.and();
        xor_negation_lemma(carry);
        assert (carry == 0 || carry == 1);
        assert (borrow == 0 || borrow == 1);

        if (carry == 0) {
            assert bv32_op_s.xor(carry, 1) == 1;
            if (borrow == 0) {
                assert select == 0;
            } else {
                assert borrow == 1;
                assert select == 1;
            }
        } else {
            assert carry == 1;
            assert bv32_op_s.xor(carry, 1) == 0;
            assert bv32_op_s.and(0, 0) == 0;
            assert bv32_op_s.and(0, 1) == 0;
            assert select == 0;
        }
    }

    lemma double_modulo_select_nosub_lemma(
        a: nat,
        aa: nat,
        carry: uint1,
        borrow: uint1,
        select: uint32,
        M: nat)
        requires 0 < M < pow_BASE(NUM_WORDS);
        requires carry == 0 ==> aa == a + a;
        requires borrow == 1 <==> aa < M;
        requires select == bv32_op_s.and(bv32_op_s.xor(carry, 1), borrow);
        requires select != 0;
        ensures aa == (a + a) % M;
    {
        double_modulo_selector_lemma(carry, borrow, select);
        assert borrow == 1;
        assert carry == 0;
        assert a + a < M;
        LemmaSmallMod(a + a, M);
    }

    lemma double_modulo_select_withsub_lemma(
        a: nat,
        aa: nat,
        carry: uint1,
        borrow: uint1,
        select: uint32,
        M: nat)
        requires a < M;
        requires 0 < M < pow_BASE(NUM_WORDS);
        requires pow_BASE(NUM_WORDS) < 2 * M;
        requires aa == a + a - carry * pow_BASE(NUM_WORDS);
        requires carry == 1 ==> a + a >= pow_BASE(NUM_WORDS);
        requires borrow == 1 <==> aa < M;
        requires select == bv32_op_s.and(bv32_op_s.xor(carry, 1), borrow);
        requires select == 0;
        ensures aa - M + borrow * pow_BASE(NUM_WORDS) == (a + a) % M;
    {
        double_modulo_selector_lemma(carry, borrow, select);
        if (carry == 1) {
          assert (borrow == 1);
          LemmaModSubMultiplesVanish(a + a, M);
          LemmaSmallMod((a + a) - M, M);
       }
       if (borrow == 0) {
          LemmaModSubMultiplesVanish(a + a, M);
          LemmaSmallMod((a + a) - M, M);
       }
    }
}

