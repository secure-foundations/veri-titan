include "../arch/riscv/machine.s.dfy"
include "bv32_ops.dfy"
include "../arch/riscv/vale.i.dfy"

include "DivModNeg.dfy"

abstract module generic_falcon_lemmas {
  
    import opened GBV: generic_bv_ops

    import opened Mul
    import opened Power
    import opened DivMod
    import opened DivModNeg
    import opened integers

    type uint = GBV.BVSEQ.uint

}

module bv32_falcon_lemmas refines generic_falcon_lemmas {
    import opened GBV = bv32_ops

    import opened rv_machine
    import opened rv_vale

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


    lemma lemma_mq_add_correct(d: uint32, b: uint32, c: uint32, r: uint32, x: int, y: int)
        requires 0 <= x < 12289;
        requires 0 <= y < 12289;
        requires d == uint32_add(to_uint32(x), uint32_add(to_uint32(y), to_uint32((-12289))));
        requires b == to_uint32(int32_rs(to_int32(d), 31));
        requires c == uint32_and(b, to_uint32(12289));
        requires r == uint32_add(c, d);
        ensures r == (x + y) % 12289;
    {
      var Q : int := 12289;

      // d == x + y - Q
      assert IsModEquivalent(d, x + y - Q, BASE_32);

      // -Q <= d < Q
      assert 0 <= x + y < 2*Q;
      assert (-Q) <= x + y - Q < Q;
      assert (-Q) <= to_int32(d) < Q;

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
        requires d == uint32_sub(to_uint32(x), to_uint32(y));
        requires b == to_uint32(int32_rs(to_int32(d), 31));
        requires c == uint32_and(b, to_uint32(12289));
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

}
