include "../../arch/riscv/machine.s.dfy"
include "../../arch/riscv/vale.i.dfy"
include "../bv32_ops.dfy"

include "../DivModNeg.dfy"
include "ntt_params.dfy"

module mq_arith_lemmas {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul
    import opened DivModNeg
    import opened integers
    import opened bv32_ops
    import opened rv_machine
    import opened rv_vale
    import opened mem
    import flat

    import opened ntt_512_params

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

    lemma lemma_mq_add_correct(d: uint32, b: uint32, c: uint32, r: uint32, x: uint32, y: uint32)
        requires 0 <= x < 12289;
        requires 0 <= y < 12289;
        requires d == uint32_add(x, uint32_add(y, to_uint32((-12289))));
        requires b == to_uint32(int32_rs(to_int32(d), 31));
        requires c == uint32_and(b, to_uint32(12289));
        requires r == uint32_add(c, d);
        ensures r == (x + y) % 12289;
    {
      assert Q == 12289;

      // d == x + y - Q
      assert IsModEquivalent(d, x + y - Q, BASE_32);

      // -Q <= d < Q
      assert 0 <= x + y < 2*Q;
      assert (-(Q as int)) <= x + y - Q < Q;
      assert (-(Q as int)) <= to_int32(d) < Q;

      if to_int32(d) >= 0 {
        assert int32_rs(to_int32(d), 31) == 0 by { lemma_rs_by_31(to_int32(d)); }
        assert uint32_and(0, Q) == 0 by { reveal_and(); }
        assert IsModEquivalent(r, x + y, Q);
      }
      else {
        assert int32_rs(to_int32(d), 31) == -1 by { lemma_rs_by_31(to_int32(d)); }
        assert uint32_and(b, Q) == Q by { reveal_and(); }
        assert IsModEquivalent(r, x + y, Q);
      }

    } 

    lemma lemma_mq_sub_correct(d: uint32, b: uint32, c: uint32, r: uint32, x: int, y: int)
        requires 0 <= x < 12289;
        requires 0 <= y < 12289;
        requires d == uint32_sub(x, y);
        requires b == to_uint32(int32_rs(to_int32(d), 31));
        requires c == uint32_and(b, 12289);
        requires r == uint32_add(c, d);
        ensures r == (x - y) % 12289;
    {
      var Q : int := 12289;
      
      assert IsModEquivalent(d, x - y, BASE_32);
      assert -Q <= to_int32(d) < 2 * Q;
      
      if to_int32(d) >= 0 {
        assert int32_rs(to_int32(d), 31) == 0 by { lemma_rs_by_31(to_int32(d)); }
        assert uint32_and(b, Q) == 0 by { reveal_and(); }
        assert IsModEquivalent(r, x - y, Q);
      }
      else {
        assert int32_rs(to_int32(d), 31) == -1 by { lemma_rs_by_31(to_int32(d)); }
        assert uint32_and(b, Q) == Q by { reveal_and(); }
        assert IsModEquivalent(r, x - y, Q);
      }
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
        requires r == to_uint32(int32_rs(to_int32(d), 1));

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
}