module mul256_lemmas {
    import opened bv_ops
    import opened ot_machine
    import opened ot_abstraction
    import opened rsa_ops

    import opened Mul
    import opened BASE_256_Seq

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
            && p0 == uint256_qmul(x, 0, y, 0)
            && p1 == uint256_qmul(x, 1, y, 0)
            && p2 == uint256_qmul(x, 0, y, 1)
            && p3 == uint256_qmul(x, 2, y, 0)
            && p4 == uint256_qmul(x, 1, y, 1)
            && p5 == uint256_qmul(x, 0, y, 2)
            && p6 == uint256_qmul(x, 3, y, 0)
            && p7 == uint256_qmul(x, 2, y, 1)
            && p8 == uint256_qmul(x, 1, y, 2)
            && p9 == uint256_qmul(x, 0, y, 3)
            && p10 == uint256_qmul(x, 3, y, 1)
            && p11 == uint256_qmul(x, 2, y, 2)
            && p12 == uint256_qmul(x, 1, y, 3)
            && p13 == uint256_qmul(x, 3, y, 2)
            && p14 == uint256_qmul(x, 2, y, 3)
            && p15 == uint256_qmul(x, 3, y, 3)
            && r0 == p0 + (p1 + p2) * B
            && r1 == uint256_uh(r0) + p3 + p4 + p5 + (p6 + p7 + p8 + p9) * B
            && r2 == uint256_uh(r1) + p10 + p11 + p12 + (p13 + p14) * B
            && r3 == uint256_uh(r2) + p15
            && t1 == uint256_hwb(t0, uint256_lh(r0), true)
            && t2 == uint256_hwb(t1, uint256_lh(r1), false)
            && u1 == uint256_hwb(u0, uint256_lh(r2), true)
            && u2 == uint256_hwb(u1, uint256_lh(r3), false)
            && wacc == uint256_uh(r3)

        ensures
            ToNat([t2, u2]) == x * y;
    {
        assert t2 == uint256_lh(r0) + uint256_lh(r1) * B2 by {
            uint256_hwb_lemma(t0, t1, t2, uint256_lh(r0), uint256_lh(r1));
        }

        assert u2 == uint256_lh(r2) + uint256_lh(r3) * B2 by {
            uint256_hwb_lemma(u0, u1, u2, uint256_lh(r2), uint256_lh(r3));
        }

        assert x == uint256_qsel(x, 0) + uint256_qsel(x, 1) * B + uint256_qsel(x, 2) * B2 + uint256_qsel(x, 3) * B3 by {
            uint256_quarter_split_lemma(x);
        }

        assert y == uint256_qsel(y, 0) + uint256_qsel(y, 1) * B + uint256_qsel(y, 2) * B2 + uint256_qsel(y, 3) * B3 by {
            uint256_quarter_split_lemma(y);
        }

        calc {
            t2 + u2 * B4 + wacc * B8;
                { uint256_half_split_lemma(r3); }
            t2 + (uint256_lh(r2) + r3 * B2) * B4;
                {
                    uint256_half_split_lemma(r2);
                    LemmaMulIsAssociativeAuto();
                }
            uint256_lh(r0) + uint256_lh(r1) * B2 + r2 * B4 + p15 * B6;
                { uint256_half_split_lemma(r1); }
            uint256_lh(r0) + r1 * B2 + (p10 + p11 + p12) * B4 + (p13 + p14) * B5 + p15 * B6;
                { uint256_half_split_lemma(r0); }
            p0 + (p1 + p2) * B + (p3 + p4 + p5) * B2 + (p6 + p7 + p8 + p9) * B3 + (p10 + p11 + p12) * B4 + (p13 + p14) * B5 + p15 * B6;
                {
                    reveal uint256_qmul();
                    LemmaMulProperties();
                }
            x * y;
        }

        assert wacc == 0 by {
            single_digit_lemma_0(x, y, B4-1);
            assert x * y <= B8;
        }

        assert ToNat([t2, u2]) == x * y by {
            LemmaSeqLen2([t2, u2]);
        }
    }
}