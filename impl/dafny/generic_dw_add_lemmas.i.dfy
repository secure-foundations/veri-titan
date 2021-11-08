include "generic_bv_ops.dfy"

abstract module generic_dw_add_lemmas {
    import opened GBV: generic_bv_ops
    import opened GBV.BVSEQ
    import opened Mul
    import opened Power
    import opened DivMod

    predicate uint_dw_add_is_safe(
        x_lh: uint, x_uh: uint,
        y_lh: uint, y_uh: uint)
    {
        ToNatRight([x_lh, x_uh]) + ToNatRight([y_lh, y_uh]) < DW_BASE()
    }

    lemma uint_dw_add_lemma(
        x_lh: uint, x_uh: uint,
        y_lh: uint, y_uh: uint,
        c1: uint1, c2: uint1,
        z_lh: uint, z_uh: uint)

        requires uint_dw_add_is_safe(x_lh, x_uh, y_lh, y_uh);
        requires (z_lh, c1) == uint_addc(x_lh, y_lh, 0);
        requires (z_uh, c2) == uint_addc(x_uh, y_uh, c1);
        
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
        requires uint_dw_add_is_safe(x_lh, x_uh, y_lh, y_uh);
    {
        var (z_lh, c1) := uint_addc(x_lh, y_lh, 0);
        var (z_uh, c2) := uint_addc(x_uh, y_uh, c1);
        uint_dw_add_lemma(x_lh, x_uh, y_lh, y_uh, c1, c2, z_lh, z_uh);
    }

    method full_mul(a: uint, b: uint) returns (lh: uint, uh: uint)
        ensures a * b == ToNatRight([lh, uh])
    {
        var full := a * b;

        assert full >= 0 by {
            LemmaMulNonnegativeAuto();
        }

        assert full < BASE() * BASE() by {
            full_mul_bound_lemma(a, b);
        }

        ghost var glh := full % BASE();
        ghost var guh := full / BASE();

        assert BASE() * guh + glh == full by {
            LemmaFundamentalDivModAuto();
        }

        if guh >= BASE() {
            assert full >= BASE() * BASE() + glh by {
                LemmaMulIsCommutativeAuto();
                LemmaMulInequalityAuto();
            }
            assert false;
        }

        assert guh >= 0 by {
            LemmaDivPosIsPos(full, BASE());
        }

        lh := full % BASE();
        uh := full / BASE();

        assert a * b == ToNatRight([lh, uh]) by {
            LemmaMulIsCommutativeAuto();
            LemmaSeqLen2([lh, uh]);
        }
    }

    lemma full_mul_bound_lemma(a: uint, b: uint)
        ensures a * b < DW_BASE();
        ensures a * b <= (BASE() - 1) * (BASE() - 1)
    {
        var full := a * b;

        assert full <= (BASE() - 1) * (BASE() - 1) by {
            LemmaMulUpperBoundAuto();
        }

        assert full < BASE() * BASE() by {
            calc <= {
                full;
                (BASE() - 1) * (BASE() - 1);
                {
                    LemmaMulIsDistributiveSubAuto();
                }
                (BASE() - 1) * BASE() - (BASE() - 1);
                {
                    LemmaMulIsCommutativeAuto();
                    LemmaMulIsDistributiveSubAuto();
                }
                BASE() * BASE() - BASE() - (BASE() - 1);
                BASE() * BASE() - 2 * BASE() + 1;
            }
        }
    }

    lemma mul_add_bound_lemma(a: uint, b: uint, c: uint)
       ensures a * b + c < DW_BASE();
    {
        var u := BASE() - 1;
        calc {
            a * b + c;
            <= { full_mul_bound_lemma(a, b); }
            u * u + c;
            <=
            u * u + u;
            == { LemmaMulIsDistributiveAddAuto(); }
            u * (u + 1); 
            <  { LemmaMulLeftInequality(u + 1, u, u + 1); }
            (u + 1) * (u + 1); 
            ==
            DW_BASE();
        }
    }
    
    method mul_add(a: uint, b: uint, c: uint) returns (lh: uint, uh: uint)
    {
        var p_lh, p_uh := full_mul(a, b);

        var res1 := uint_addc(p_lh, c, 0);
        var res2 := uint_addc(p_uh, 0, res1.1);
        lh, uh := res1.0, res2.0;

        mul_add_bound_lemma(a, b, c);

        assert ToNatRight([c, 0]) == c by {
            LemmaSeqLen2([c, 0]);
            assert ToNatRight([c, 0]) == c + 0 * BASE();
        }
        uint_dw_add_lemma(p_lh, p_uh, c, 0, res1.1, res2.1, lh, uh);
    }

    lemma mul_double_add_bound_lemma(a: uint, b: uint, c: uint, d: uint)
        ensures a * b + c + d < DW_BASE();
    {
        var u := BASE() - 1;

        calc {
            a * b + c + d;
            <= { full_mul_bound_lemma(a, b); }
            u * u + c + d;
            <= u * u + u + u;
            u * u + 2 * u;
            < (u * u) + (2 * u) + 1;
        }

        calc == {
            (u + 1) * (u + 1);
            { LemmaMulIsDistributiveAdd(u + 1, u, 1); }
            (u + 1) * u + (u + 1) * 1; 
            u * (u + 1) + u + 1;
            { LemmaMulIsDistributiveAdd(u, u, 1); }
            (u * u) + (2 * u) + 1;
        }
    }
}