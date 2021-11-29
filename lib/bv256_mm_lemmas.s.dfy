include "../arch/otbn/abstraction.i.dfy"
include "bv256_ops.dfy"
include "generic_mm_lemmas.dfy"
include "mul256_nl_lemma.i.dfy"

module bv256_mm_lemmas refines generic_mm_lemmas {
    import opened GBV = bv256_ops
    import opened ot_machine
    import opened ot_abstraction
    import opened mul256_nl_lemma

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
        && buff_base_ptr_valid(heap, out_ptr)
        && |heap[out_ptr].b| == NUM_WORDS

        && out_ptr != m0d_ptr
        && out_ptr != rr_ptr
        && out_ptr != m_ptr
        && out_ptr != sig_ptr
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

        var x_0, x_1, x_2, x_3  := otbn_qsel(x, 0), otbn_qsel(x, 1), otbn_qsel(x, 2), otbn_qsel(x, 3);

        assert x == x_0 + x_1 * B + x_2 * B2 + x_3 * B3 by {
            uint256_quarter_split_lemma(x);
        }

        var y_0, y_1, y_2, y_3  := otbn_qsel(y, 0), otbn_qsel(y, 1), otbn_qsel(y, 2), otbn_qsel(y, 3);

        assert y == y_0 + y_1 * B + y_2 * B2 + y_3 * B3 by {
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
            lh(r0) + (r1 - uh(r1) * B2) * B2 + r2 * B4 + p15 * B6;
            lh(r0) + r1 * B2 - uh(r1) * B4 + r2 * B4 + p15 * B6;
            lh(r0) + r1 * B2 + (r2 - uh(r1)) * B4 + p15 * B6;
            lh(r0) + r1 * B2 + (p10 + p11 + p12 + (p13 + p14) * B) * B4 + p15 * B6;
            lh(r0) + r1 * B2 + ((p10 + p11 + p12) + (p13 + p14) * B) * B4 + p15 * B6;
                { LemmaMulIsDistributiveAddOtherWayAuto(); }
            lh(r0) + r1 * B2 + (p10 + p11 + p12) * B4 + ((p13 + p14) * B) * B4 + p15 * B6;
                { LemmaMulIsCommutativeAuto(); }
            lh(r0) + r1 * B2 + (p10 + p11 + p12) * B4 + (p13 + p14) * B5 + p15 * B6;
                { half_split_lemma(r0); }
            p0 + (p1 + p2) * B + (p3 + p4 + p5) * B2 + (p6 + p7 + p8 + p9) * B3 + (p10 + p11 + p12) * B4 + (p13 + p14) * B5 + p15 * B6;
                {
                    reveal otbn_qmul();
                    mul256_canonize_lemma(
                        p0, p1, p2, p3,
                        p4, p5, p6, p7,
                        p8, p9, p10, p11,
                        p12, p13, p14, p15,
                        x, x_0, x_1, x_2, x_3,
                        y, y_0, y_1,y_2, y_3);
                }
            x * y;
        }

        assert wacc == 0 by {
            assert x * y <= (B4 - 1) * (B4 - 1) by {
                Mul.LemmaMulUpperBoundAuto();
            }
            assert x * y <= B8;
        }

        assert to_nat([t2, u2]) == x * y by {
            GBV.BVSEQ.LemmaSeqLen2([t2, u2]);
        }
    }
}

