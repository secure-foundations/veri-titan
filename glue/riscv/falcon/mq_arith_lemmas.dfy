include "../../../spec/arch/riscv/machine.s.dfy"
include "../../../spec/bvop/bv32_op.s.dfy"
include "../../../spec/arch/riscv/vale.i.dfy"

include "../../../misc/DivModNeg.dfy"
include "../../../spec/crypto/falcon512.i.dfy"

module mq_arith_lemmas {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul
    import opened DivModNeg
    import opened integers
    import opened bv32_op_s
    import opened rv_machine
    import opened rv_vale
    import opened mem
    import flat

    import opened falcon_512_i

    lemma {:axiom} rs1_is_half(a: uint32)
        ensures uint32_rs(a, 1) == a / 2;

    lemma {:axiom} ls1_is_double(a: uint32)
        requires a < BASE_31;
        ensures uint32_ls(a, 1) == a * 2;

    lemma lemma_rs_by_31(x: int32)
        ensures x >= 0 ==> int32_rs(x, 31) == 0;
        ensures x < 0 ==> int32_rs(x, 31) == -1;
    {
        assert integers.BASE_31 == Power2.Pow2(31) by { Power2.Lemma2To64(); }

        if x >= 0 {
            assert x / Power2.Pow2(31) == 0 by {
                DivMod.LemmaBasicDivAuto();
            }
        } else {
            assert x / Power2.Pow2(31) == -1 by {
                DivModNeg.LemmaDivBounded(x, integers.BASE_31);
            }
        }
    }

    lemma cond_set_Q_lemma(a: uint32, b: uint32)
        requires b == uint32_and(uint32_srai(a, 31), Q);
        ensures b == if to_int32(a) >= 0 then 0 else Q;
    {
        if to_int32(a) >= 0 {
            calc == {
                b;
                uint32_and(uint32_srai(a, 31), Q);
                uint32_and(to_uint32(int32_rs(to_int32(a), 31)), Q);
                {
                    lemma_rs_by_31(to_int32(a));
                    assert int32_rs(to_int32(a), 31) == 0;          
                }
                uint32_and(to_uint32(0), Q);
                uint32_and(0, Q);
                {
                    lemma_and_with_constants(Q);
                }
                0;
            }
        } else {
            calc == {
                b;
                uint32_and(uint32_srai(a, 31), Q);
                uint32_and(to_uint32(int32_rs(to_int32(a), 31)), Q);
                {
                    lemma_rs_by_31(to_int32(a));
                    assert int32_rs(to_int32(a), 31) == -1;
                }
                uint32_and(to_uint32(-1), Q);
                {
                    lemma_and_with_constants(Q);
                }
                Q;
            }
        }
    }

    lemma lemma_mq_add_correct(d: uint32, b: uint32, c: uint32, r: uint32, x: uint32, y: uint32)
        requires 0 <= x < 12289;
        requires 0 <= y < 12289;
        requires d == uint32_add(x, uint32_add(y, to_uint32((-12289))));
        requires b == uint32_srai(d, 31);
        requires c == uint32_and(b, Q);
        requires r == uint32_add(c, d);
        ensures r == (x + y) % 12289;
    {
        cond_set_Q_lemma(d, c);
    } 

    lemma lemma_uint32_and_Q(x: uint32)
        ensures x == 0 ==> uint32_and(x, Q) == 0;
        ensures to_int32(x) == -1 ==> uint32_and(x, Q) == Q;
    {
        reveal_and();
        if to_int32(x) == - 1{
            assert x == 4294967295;
            assert uint32_and(4294967295, Q) == Q;
        }
    }

    lemma lemma_mq_sub_correct(d: uint32, b: uint32, c: uint32, r: uint32, x: int, y: int)
        requires 0 <= x < 12289;
        requires 0 <= y < 12289;
        requires d == uint32_sub(x, y);
        requires b == uint32_srai(d, 31);
        requires c == uint32_and(b, 12289);
        requires r == uint32_add(c, d);
        ensures r == (x - y) % 12289;
    {
        cond_set_Q_lemma(d, c);
    }

    lemma lemma_positive_rs(x: uint32, shift: nat)
      requires x >= 0;
      requires x < BASE_31;
      ensures to_uint32(int32_rs(x, shift)) == int32_rs(x, shift)
    {
        assert to_int32(x) == x;
        assert int32_rs(to_int32(x), shift) >= 0 by { DivMod.LemmaDivBasicsAuto(); }
    }

    lemma lemma_mq_rshift1_correct(par: uint32, b: uint32, c: uint32, d: uint32, r: uint32, x: int)
        requires 0 <= x < 12289;
        requires par == uint32_and(x, 1);
        requires b == uint32_sub(0, par);
        requires c == uint32_and(b, 12289);
        requires d == uint32_add(x, c);
        requires r == uint32_srai(d, 1);

        //ensures r == (x / 2) % 12289;
        ensures IsModEquivalent(2 * r, x, 12289);
        ensures r < 12289;
    {
        var Q : int := 12289;
        assert par == 0 || par == 1 by { reveal_and(); }
 
        if par == 0 {
            assert b == 0;
            assert c == 0 by { reveal_and(); }
            assert x % 2 == 0 by { reveal_and(); }
            assert d == x;
            
            assert 0 <= to_int32(d) < Q;
            assert r == int32_rs(to_int32(d), 1) by { lemma_positive_rs(x, 1); }
    
            assert r == d / Power2.Pow2(1);
            assert r == d / 2 by { Power2.Lemma2To64(); }
    
            assert IsModEquivalent(r, x / 2, Q);
        } else {
            assert b == 0xffff_ffff;
            assert c == Q by { reveal_and(); }
            assert d == uint32_add(x, Q);
            assert d == x + Q;

            assert 0 <= to_int32(d) <= x + Q;
            assert r == int32_rs(to_int32(d), 1) by { lemma_positive_rs(x + Q, 1); }
    
            assert IsModEquivalent(d, x, Q);
    
            assert r == d / Power2.Pow2(1);
            assert r == d / 2 by { Power2.Lemma2To64(); }
    
            assert r == (x + Q) / 2;
            
            //  assert x % 2 == 1 by { reveal_and(); }
            assume x % 2 == 1;
            assert Q % 2 == 1;
            assert (x + Q) % 2 == 0 by { DivMod.LemmaModAdds(x, Q, 2); }
    
            assert r == (x + Q) / 2;
            assert IsModEquivalent(2 * r, x + Q, Q);
        }
    }

    lemma lemma_shiftmul3(a: nat, b: nat, ab: nat, ab3: nat)
        requires a < Q;
        requires b < Q;
        requires ab == uint32_mul(a, b)
        requires ab3 == uint32_add(uint32_ls(ab, 1), ab);
        ensures ab3 == 3 * a * b;
        ensures ab3 == 3 * ab;
        ensures ab == a * b;
        ensures ab <= (Q-1) * (Q-1);
    {
        reveal dw_lh();
        Mul.LemmaMulNonnegative(a, b);
        Mul.LemmaMulUpperBound(a, Q-1, b, Q-1);
        DivMod.LemmaSmallMod(a * b, BASE_32);

        assert a * b == ab;
        assert ab3 == 3 * ab by { ls1_is_double(ab); }
        assert ab3 == 3 * a * b by { Mul.LemmaMulIsAssociativeAuto(); }
    }

    lemma lemma_12289(v: uint32, v3: uint32, w: uint32)
      requires v < BASE_16;
      requires v3 == 3 * v;
      requires w == uint32_add(uint32_ls(v3, 12), v);
      ensures w == Q * v;
      ensures w <= Q * (BASE_16 - 1);
    {
        var lsv3 := uint32_ls(v3, 12);
        assert lsv3 == (v3 * Power2.Pow2(12)) % BASE_32 by { ls_is_mul_mod_base(v3, 12); }
        assert lsv3 == (3 * v * Power2.Pow2(12)) % BASE_32 by { Mul.LemmaMulIsAssociativeAuto(); }

        var lsv3_int := lsv3 as int;
        
        gbassert IsModEquivalent(w, 12289 * v, BASE_32) by {
            assert IsModEquivalent(lsv3_int, 3 * v * 4096, BASE_32) by {
                Power2.Lemma2To64();
            }
            assert IsModEquivalent(w, lsv3_int + v, BASE_32);
        }
    }

    lemma lemma_zw_shift(w: uint32, xy: uint32, z:uint32)
        requires w <= Q * (BASE_16 - 1);
        requires xy <= (Q-1) * (Q-1);
        requires z == uint32_rs(uint32_add(w, xy), 16);
        ensures z == uint32_rs(w + xy, 16);
        ensures z < 2 * Q; 
    {
        var wxy := uint32_add(w, xy);
        assert wxy == w + xy;

        assert z == uint32_rs(wxy, 16);
        assert z == (wxy / Power2.Pow2(16)) % BASE_32 by { rs_is_div_mod_base(wxy, 16); }

        assert wxy <= Q * (BASE_16 - 1) + (Q-1) * (Q-1);
        assert z == (wxy / Power2.Pow2(16)) by {
            DivMod.LemmaDivNonincreasing(wxy, Power2.Pow2(16));
            DivMod.LemmaDivPosIsPos(wxy, Power2.Pow2(16));
            DivMod.LemmaSmallMod((wxy / Power2.Pow2(16)), BASE_32);
        }
        
        assert z <= (Q * (BASE_16 - 1) + (Q-1) * (Q-1)) / Power2.Pow2(16) by {
            DivMod.LemmaDivIsOrdered(wxy, Q * (BASE_16 - 1) + (Q-1) * (Q-1), Power2.Pow2(16));
        }

        assert z <= 14592 by { Power2.Lemma2To64(); }
        assert 14592 < 2 * Q;
    }

    lemma lemma_Q0Ixy_correct(x: nat, y: nat, xy: uint32, xy3: uint32, Q0Ixy: nat)
        requires x < Q;
        requires y < Q;
        requires xy < Q * Q;
        requires xy as nat == x * y;
        requires xy3 as nat == 3 * x * y;
        requires Q0Ixy == uint32_sub(uint32_ls(xy3, 12), xy);
        ensures IsModEquivalent(Q0Ixy, 12287 * x * y, BASE_32);
        ensures IsModEquivalent(12287 * x * y, 12287 * xy, BASE_32);
    {
        var sh := uint32_ls(xy3, 12);
        assert sh == (xy3 * Power2.Pow2(12)) % BASE_32 by { ls_is_mul_mod_base(xy3, 12); }

        var sh_int := sh as int;
        var xy_int := xy as int;
        
        gbassert IsModEquivalent(Q0Ixy, 12287 * x * y, BASE_32) by {
            assert xy3 == 3 * x * y;
            assert xy_int == x * y;
            assert IsModEquivalent(sh_int, xy3 * 4096, BASE_32) by { Power2.Lemma2To64(); }
            assert IsModEquivalent(Q0Ixy, sh_int - xy_int, BASE_32);
        }

        gbassert IsModEquivalent(12287 * x * y, 12287 * xy_int, BASE_32) by {
            assert xy_int == x * y;
        }
    }

    lemma lemma_shiftadd3(Q0Ixy:uint32, v: uint32, v3: nat)
        requires v == uint32_rs(uint32_ls(Q0Ixy, 16), 16);
        requires v3 == uint32_add(uint32_ls(v, 1), v);
        ensures IsModEquivalent(v, Q0Ixy, BASE_16);
        ensures v < BASE_16; 
        ensures v3 == 3 * v;
    {
        var lsx := uint32_ls(Q0Ixy, 16);
        assert lsx == (Q0Ixy * Power2.Pow2(16)) % BASE_32 by { ls_is_mul_mod_base(Q0Ixy, 16); }
        
        assert v == (lsx / Power2.Pow2(16)) % BASE_32 by { rs_is_div_mod_base(lsx, 16); }
        assert v < BASE_32;
        assert v == (lsx / Power2.Pow2(16)) by {
            DivMod.LemmaDivNonincreasing(lsx, Power2.Pow2(16));
            DivMod.LemmaDivPosIsPos(lsx, Power2.Pow2(16));
            DivMod.LemmaSmallMod((lsx / Power2.Pow2(16)), BASE_32);
        }
        assert v < BASE_16 by {
            Power2.Lemma2To64();
            DivMod.LemmaDivIsOrdered(lsx, BASE_32, BASE_16);
        }

        assert v3 == v * 3 by { ls1_is_double(v); }

        assert IsModEquivalent(v * BASE_16, Q0Ixy * BASE_16, BASE_32) by { Power2.Lemma2To64(); }
        assert BASE_16 * BASE_16 == BASE_32;// by { Power2.Lemma2To64(); }

        calc {
            (v * BASE_16) % BASE_32;
                { LemmaModBreakdown(v * BASE_16, BASE_16, BASE_16); }
            BASE_16 * (((v * BASE_16) / BASE_16) % BASE_16) + (v * BASE_16) % BASE_16;
                { LemmaModMultiplesBasic(v, BASE_16); }
            BASE_16 * (((v * BASE_16) / BASE_16) % BASE_16);
                { LemmaDivMultiplesVanish(v, BASE_16); }
            BASE_16 * (v % BASE_16);
        }

        calc {
            (Q0Ixy * BASE_16) % BASE_32;
                { LemmaModBreakdown(Q0Ixy * BASE_16, BASE_16, BASE_16); }
            BASE_16 * (((Q0Ixy * BASE_16) / BASE_16) % BASE_16) + (Q0Ixy * BASE_16) % BASE_16;
                { LemmaModMultiplesBasic(Q0Ixy, BASE_16); }
            BASE_16 * (((Q0Ixy * BASE_16) / BASE_16) % BASE_16);
                { LemmaDivMultiplesVanish(Q0Ixy, BASE_16); }
            BASE_16 * (Q0Ixy % BASE_16);
        }

        assert BASE_16 * (v % BASE_16) == BASE_16 * (Q0Ixy % BASE_16);
        assert (BASE_16 * (v % BASE_16))/BASE_16 == (BASE_16 * (Q0Ixy % BASE_16))/BASE_16;
        assert v % BASE_16 == Q0Ixy % BASE_16 by {
            LemmaDivMultiplesVanish(v % BASE_16, BASE_16);
            LemmaDivMultiplesVanish(Q0Ixy % BASE_16, BASE_16);
        }
    }

    lemma lemma_and_with_constants(x: uint32)
        ensures uint32_and(0, x) == 0;
        ensures uint32_and(0xffff_ffff, x) == x;
    {
        reveal_and();
    }

    lemma lemma_cond_add_Q(z: uint32, d: uint32, b: uint32, c: uint32, r: uint32)
        requires z < 2 * Q;
        requires d == uint32_sub(z, Q);
        requires b == uint32_srai(d, 31);
        requires c == uint32_and(b, Q);
        requires r == uint32_add(c, d);
        ensures r < Q;
        ensures r == z % Q;
    {
        cond_set_Q_lemma(d, c);
    }

    lemma lemma_montymul_correct(x: nat, y: nat, xy: uint32, Q0Ixy:nat, v: nat, w: uint32, z: uint32, rr: uint32)
        requires x < Q;
        requires y < Q;
        requires xy == x * y;
        requires IsModEquivalent(Q0Ixy, 12287 * x * y, BASE_32);
        requires IsModEquivalent(v, Q0Ixy, BASE_16);
        requires v < BASE_16;
        requires w == Q * v;
        requires w as nat + xy as nat < BASE_32;
        requires z == uint32_rs(w + xy, 16);
        requires z < 2 * Q;
        requires rr == z % Q;
        ensures IsModEquivalent(rr * 4091, x * y, Q);
        ensures rr == MQP.montmul(x, y);
    {
        gbassert IsModEquivalent(v, 12287 * x * y, BASE_16) by {
            assert IsModEquivalent(Q0Ixy, 12287 * x * y, BASE_32);
            assert IsModEquivalent(v, Q0Ixy, BASE_16);
            assert BASE_16 == 65536;
            assert BASE_32 == 0x1_0000_0000;
        }

        gbassert IsModEquivalent(w + xy, 0, BASE_16) by {
            assert IsModEquivalent(v, 12287 * x * y, BASE_16);
            assert Q == 12289;
            assert BASE_16 == 65536;
            assert w == Q * v;
            assert xy == x * y;
        }

        DivMod.LemmaFundamentalDivMod(w + xy, BASE_16);
        rs_is_div_mod_base(w + xy, 16);
        Power2.Lemma2To64();
        assert z * BASE_16 == w + xy;

        gbassert IsModEquivalent(rr * 4091, x * y, Q) by {
            assert IsModEquivalent(v, 12287 * x * y, BASE_16);
            assert Q == 12289;
            assert BASE_16 == 65536;
            assert IsModEquivalent(4091, BASE_16, Q);
            assert w == Q * v;
            assert xy == x * y;
            assert z * BASE_16 == (w + xy);
            assert IsModEquivalent(w + xy, 0, BASE_16);
            assert IsModEquivalent(rr, z, Q);
        }

        assume rr == MQP.montmul(x, y);
    }

    // lemma mul_upper_bound_Qsquared(x: nat, y: nat)
    //     requires x <= 12289;
    //     requires y <= 12289;
    //     requires 0 <= x
    //     requires 0 <= y
    //     ensures mul(x, y) == x * y;
    //     ensures x * y <= 151019521;
    // {
    //     reveal dw_lh();
    //     Mul.LemmaMulNonnegative(x, y);
    //     Mul.LemmaMulUpperBound(x, 12289, y, 12289);
    //     DivMod.LemmaSmallMod(x * y, BASE_32);
    // }
}
