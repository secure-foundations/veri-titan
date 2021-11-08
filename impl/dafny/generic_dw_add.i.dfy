include "../../lib/generic_bv_ops.dfy"
include "../../lib/bv256_ops.dfy"

abstract module generic_dw_add {
    import opened GBV: generic_bv_ops
    import opened BVSEQ = GBV.BVSEQ
    import opened Mul
    import opened Power
    import opened DivMod
    import integers

    // type uint = GBV.BVSEQ.uint

    predicate dw_add_is_safe(
        x_lh: uint, x_uh: uint,
        y_lh: uint, y_uh: uint)
    {
        ToNatRight([x_lh, x_uh]) + ToNatRight([y_lh, y_uh]) < DW_BASE()
    }

    lemma dw_add_lemma(
        x_lh: uint, x_uh: uint,
        y_lh: uint, y_uh: uint,
        c1: integers.uint1, c2: integers.uint1,
        z_lh: uint, z_uh: uint)

        requires dw_add_is_safe(x_lh, x_uh, y_lh, y_uh);
        requires (z_lh, c1) == GBV.addc(x_lh, y_lh, 0);
        requires (z_uh, c2) == GBV.addc(x_uh, y_uh, c1);
        
        ensures ToNatRight([z_lh, z_uh]) == ToNatRight([x_lh, x_uh]) + ToNatRight([y_lh, y_uh]);
    {
        var x_full := ToNatRight([x_lh, x_uh]);
        var y_full := ToNatRight([y_lh, y_uh]);
        var z_full := ToNatRight([z_lh, z_uh]);

        assert SeqAdd([x_lh], [y_lh]) == ([z_lh], c1) by {
            reveal SeqAdd();
            assert [] + [z_lh] == [z_lh];
        }

        assert SeqAdd([x_lh, x_uh], [y_lh, y_uh]) == ([z_lh, z_uh], c2) by {
            reveal SeqAdd();
            assert [z_lh] + [z_uh] == [z_lh, z_uh];
        }

        assert ToNatRight([z_lh, z_uh]) + c2 * Pow(BASE(), 2) == x_full + ToNatRight([y_lh, y_uh]) by {
            LemmaSeqAdd([x_lh, x_uh], [y_lh, y_uh], [z_lh, z_uh], c2);
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
}

module bv256_dw_add refines generic_dw_add {
    import opened GBV = bv256_ops
    import opened BVSEQ = bv256_seq
}