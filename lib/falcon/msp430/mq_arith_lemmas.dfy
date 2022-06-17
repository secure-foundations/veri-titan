include "../../../arch/msp430/machine.s.dfy"
include "../../../arch/msp430/vale.i.dfy"
include "../../bv16_ops.dfy"
include "../mq_polys.dfy"

//include "../DivModNeg.dfy"
include "../ntt_params.dfy"

module mq_arith_lemmas {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul
    import opened integers
    import opened bv16_ops
    import opened msp_machine
    import opened msp_vale
    import opened mq_polys
    import opened ntt_512_params
    //import opened mem
    //import flat

    lemma lemma_mq_add_correct(sum: uint16, mask: uint16, r: uint16, x: uint16, y: uint16)
        requires 0 <= x < 12289;
        requires 0 <= y < 12289;
        requires sum == msp_add(x, msp_add(y, 0xcfff).0).0;
        requires mask == msp_sub(0, if sum >= 0x8000 then 1 else 0).0;
        requires r == msp_add(sum, uint16_and(12289, mask)).0;
        ensures r == mqadd(x, y);
    {
      assert Q == 12289;

      // d == x + y - Q
      assert IsModEquivalent(sum, x + y - Q, BASE_16);

      // -Q <= d < Q
      assert 0 <= x + y < 2*Q;
      assert (-(Q as int)) <= x + y - Q < Q;

      if sum >= 0x8000 {
        assert mask == 0xFFFF;
        assert uint16_and(Q, 0xFFFF) == Q by { reveal_and(); }
        assert IsModEquivalent(r, x + y, Q);
      } else {
        assert mask == 0;
        assert uint16_and(Q, 0) == 0 by { reveal_and(); }
        assert IsModEquivalent(r, x + y, Q);
      }

    } 

    lemma lemma_mq_sub_correct(diff: uint16, flags: flags_t, mask: uint16, r: uint16, x: int, y: int)
        requires 0 <= x < 12289;
        requires 0 <= y < 12289;
        requires var (d, f) := msp_sub(x, y);
                 diff == d && flags == f;
        requires mask == msp_sub(0, if x - y >= 0 then 0 else 1).0;
        requires var (s, _) := msp_subc(0, 0xFFFF, flags);
                 mask == s;
        requires r == msp_add(diff, uint16_and(12289, mask)).0;
        ensures r == mqsub(x, y);
    {
      var Q : int := 12289;
      
      assert IsModEquivalent(diff, x - y, BASE_16);
      
      if get_cf(flags) == 0 {
        assert mask == 0xFFFF;
        assert uint16_and(Q, 0xFFFF) == Q by { reveal_and(); }
        assert IsModEquivalent(r, x - y, Q);
      } else {
        assert mask == 0;
        assert uint16_and(Q, 0) == 0 by { reveal_and(); }
        assert IsModEquivalent(r, x - y, Q);
      }
    }

    lemma lemma_cond_add_Q(flags: flags_t, mask: uint16, r: uint16, input: uint16)
        requires mask == msp_sub(0, if get_cf(flags) == 1 then 1 else 0).0;
        requires var (s, _) := msp_subc(0, 0, flags);
                 mask == s;
        requires r == msp_add(input, uint16_and(12289, mask)).0;
        ensures r == input + if get_cf(flags) == 1 then Q else 0;
    {
      assume false;
    }


//    lemma lemma_cond_add_Q(
//        z: uint16, d: uint16, b: uint16, c: uint16, r: uint16)
//         requires z < 2 * Q;
//         requires d == msp_sub(z, Q);
//         requires b == to_msp(int32_rs(to_int32(d), 31));
//         requires c == msp_and(b, Q);
//         requires r == msp_add(c, d);
//         ensures r < Q;
//         ensures r == z % Q;
//     {
//
//      if to_int32(d) >= 0 {
//        assert int32_rs(to_int32(d), 31) == 0 by { lemma_rs_by_31(to_int32(d)); }
//        assert uint16_and(0, Q) == 0 by { lemma_and_with_constants(Q); }
//        assert IsModEquivalent(r, z, Q);
//      }
//      else {
//        assert int32_rs(to_int32(d), 31) == -1 by { lemma_rs_by_31(to_int32(d)); }
//        assert uint16_and(b, Q) == Q by { lemma_and_with_constants(Q); }
//        assert IsModEquivalent(r, z, Q);
//      }
//     }
/*
     lemma lemma_montymul_correct(x: nat, y: nat, xy: uint16, Q0Ixy:nat, v: nat, w: uint16, z: uint16, rr: uint16)
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
     }
*/
}
