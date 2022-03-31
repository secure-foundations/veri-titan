include "../arch/riscv/machine.s.dfy"
include "bv32_ops.dfy"
include "../arch/riscv/vale.i.dfy"

abstract module generic_falcon_lemmas {
  
    import opened GBV: generic_bv_ops

    import opened Mul
    import opened Power
    import opened DivMod
    import opened integers

    type uint = GBV.BVSEQ.uint

}

module bv32_falcon_lemmas refines generic_falcon_lemmas {
    import opened GBV = bv32_ops

    import opened rv_machine
    import opened rv_vale

    lemma lemma_mq_add_correct(d: uint32, b: uint32, c: uint32, r: uint32, x: uint32, y: uint32)
        requires x < 12289;
        requires y < 12289;
        requires d == uint32_add(to_uint32(x), uint32_add(to_uint32(y), to_uint32((-12289))));
        requires b == to_uint32(int32_rs(to_int32(d), 31));
        requires c == uint32_and(b, to_uint32(12289));
        requires r == uint32_add(c, d);
        ensures r == (x + y) % 12289;
    {
      var Q : uint32 := 12289;

      // 2 goals:
      // (1) r < 12289
      // (2) IsModEquivalent(r, x + y, Q)

      // d == x + y - Q
      assert IsModEquivalent(d, x + y - Q, BASE_32);

      if to_int32(d) > 0 {
        assert uint32_rs(to_int32(d), 31) == 0 by {
          calc { d / Power2.Pow2(31); }
        }
      } else {
        assert uint32_rs(to_int32(d), 31) == -1 by {
          calc { d / Power2.Pow2(31); }
        }
      }
      
      // r == d - Q


      assume IsModEquivalent(r, x + y, Q * BASE_32);
      assume r < 12289;
    } 

}
