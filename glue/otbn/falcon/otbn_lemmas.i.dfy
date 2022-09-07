include "../../arch/otbn/machine.s.dfy"
include "../../arch/otbn/vale.i.dfy"
include "ntt_params.dfy"

module otbn_lemmas {
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul
    import opened integers
    import opened bv32_op_s
    import opened ot_machine
    import opened ot_vale
    import opened mem
    import flat

    import opened ntt_512_params


    lemma addm_correct_lemma(x: uint256, y:uint256, mod: uint256)
      requires x < mod;
      requires y < mod;
      ensures 0 <= otbn_addm(x, y, mod) < mod;
      ensures otbn_addm(x, y, mod) == (x + y) % mod;
    {
      assert (x + y) < 2 * mod;

      if (x + y) < mod {
        assert (x + y) % mod == otbn_addm(x, y, mod) by { DivMod.LemmaSmallMod((x + y), mod); }
      } else { 
        assert mod <= x + y < 2 * mod;
        
        calc == {
          otbn_addm(x, y, mod);
          (x + y - mod) % BASE_256;
          { assert x + y - mod < BASE_256; }
          (x + y - mod);
          {
            assert 0 <= x + y - mod < mod;
            DivMod.LemmaSmallMod(x + y - mod, mod);
          }
          (x + y - mod) % mod;
          { DivMod.LemmaModSubMultiplesVanishAuto(); }
          (x + y) % mod;
        }
      }
    }

    lemma subm_correct_lemma(x: uint256, y: uint256, mod: uint256)
      requires x < mod;
      requires y < mod;
      ensures 0 <= otbn_subm(x, y, mod) < mod;
      ensures otbn_subm(x, y, mod) == (x - y) % mod;
    {
      var diff : int := x as int - y as int;
      assert -(mod as int) < diff < mod;

      if diff >= 0 {
        assert diff < mod;
        assert diff % mod == otbn_subm(x, y, mod) by { DivMod.LemmaSmallMod(diff, mod); }
      } else {

        calc == {
          otbn_subm(x, y, mod);
          (diff + mod) % BASE_256;
          { assert 0 <= diff + mod < BASE_256; }
          (diff + mod);
          {
            assert 0 <= diff + mod < mod;
            DivMod.LemmaSmallMod(diff + mod, mod);
          }
          (diff + mod) % mod;
          { DivMod.LemmaModAddMultiplesVanish(diff, mod); }
          diff % mod;
        }
      }
    }

    lemma lemma_elem_prod_bound(x: uint256, y: uint256, r: uint256)
      requires x < 12289 && y < 12289
      requires r == x * y
      ensures r <= 150994944
    {
      LemmaMulUpperBound(x, 12288, y, 12288);
    }

    lemma lemma_small(x:uint256)
      requires x < BASE_64
      ensures bv256_op_s.lh(x) % BASE_64 == x
    {
      calc{
        bv256_op_s.lh(x) % BASE_64;
          { reveal bv256_op_s.lh(); }
        (x % BASE_256) % BASE_64;
          { LemmaSmallMod(x, BASE_256); }
        x % BASE_64;
          { LemmaSmallMod(x, BASE_64); }
        x;
      }
    }


    lemma lemma_small_mulqacc(x: uint256, y: uint256, r: uint256, old_wacc: uint256, old_flags: flags_t)
      requires x < BASE_64 && y < BASE_64
      requires var product := otbn_mulqacc(true, x, 0, y, 0, 0, old_wacc);
               r == otbn_mulqacc_so(product, 0, true, old_flags).new_dst
      ensures r == x * y
    {
      LemmaMulUpperBound(x, BASE_64 - 1, y, BASE_64 - 1);
      var product := otbn_mulqacc(true, x, 0, y, 0, 0, old_wacc);
      calc {
        product;
        otbn_shift(otbn_qmul(x, 0, y, 0), SFT(true, 0 * 8));
        otbn_shift(otbn_qmul(x, 0, y, 0), SFT(true, 0));
        otbn_qmul(x, 0, y, 0);
          { reveal otbn_qmul(); }
        otbn_qsel(x, 0) as uint128 * otbn_qsel(y, 0) as uint128;
          { reveal otbn_qsel(); }
        ((bv256_op_s.lh(x) % BASE_64) as uint128) * ((bv256_op_s.lh(y) % BASE_64) as uint128);
          { lemma_small(x); lemma_small(y); }
        x as uint128 * y as uint128;
        x * y;
      }
      
      calc {
        bv256_op_s.lh(product);
          { reveal bv256_op_s.lh(); LemmaSmallMod(x, BASE_256); }
        x * y;
      }
      
      calc {
        otbn_hwb(0, x * y, true);
          { reveal otbn_hwb(); }
        x * y + bv256_op_s.uh(0) * BASE_128;
          { reveal bv256_op_s.uh(); }
        x * y;
      }
    }

    lemma lemma_montymul_correct(x: uint256, y: uint256, prod: uint256, sum: uint256, 
                                 shifted: uint256, diff1: uint256, flags: flags_t, diff2: uint256)
      requires 0 <= x * y <= 150994944 
      requires prod == (x * y) * (Q * (Q-2))
      requires sum == otbn_addc(prod, x*y, SFT_DFT, false).0;
      requires shifted == otbn_addc(0, sum, SFT(false, 2), false).0;
      requires diff1 == otbn_subb(shifted, Q, SFT_DFT, false).0;
      requires flags == otbn_subb(shifted, Q, SFT_DFT, false).1;
      requires diff2 == otbn_addc(diff1, if flags.get_single_flag(0) then Q else 0, SFT_DFT, false).0;
      ensures IsModEquivalent(diff2 * 4091, x * y, 12289);
    {
      assert prod <= 22799472962568192 by { LemmaMulUpperBound(x * y, 150994944, Q * (Q-2), 150994943); }
      assert sum == prod + x * y;
      assert 0 <= sum < BASE_256;
      calc {
        shifted;
        bv256_op_s.rs(sum, 16);
          { bv256_op_s.rs_is_div_mod_base(sum, 16); }
        (sum / Power2.Pow2(16)) % BASE_256;
          { Lemma2To64(); }
        (sum / BASE_16) % BASE_256;
        sum / BASE_16;
      }

      gbassert IsModEquivalent(sum, 0, BASE_16) by {
          assert Q == 12289;
          assert BASE_16 == 65536;
          assert prod == (x * y) * (Q * (Q-2));
          assert sum == prod + x * y;
      }

      gbassert IsModEquivalent(diff2 * 4091, x * y, Q) by {
        assert Q == 12289;
        assert BASE_16 == 65536;
        assert prod == (x * y) * (Q * (Q-2));
        assert sum == prod + x * y;
        assert IsModEquivalent(4091, BASE_16, Q);
        assert shifted * BASE_16 == sum; 
        assert IsModEquivalent(sum, 0, BASE_16);
        assert IsModEquivalent(diff2, shifted, Q);
      }
    }

    predicate {:opaque} contains_elems(a: seq<nat>)
        ensures contains_elems(a) ==> |a| == N.full;
    {
        && (|a| == N.full)
        && (forall i | 0 <= i < N.full :: a[i] < Q)
    }

    predicate fvar_iter_inv(heap: heap_t, iter: b256_iter, address: int, index: int)
    {
        && b256_iter_inv(heap, iter) //, if address >= 0 then address else iter.cur_ptr())
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && contains_elems(iter.buff)
    }

    function {:opaque} as_elems(a: seq<uint256>): (a': elems)
        requires contains_elems(a);
        ensures a == a';
    {
        reveal contains_elems();
        a
    }
    
    function mqsub(f: uint256, g: uint256) : uint256
    {
      (f - g) % Q
    }

    predicate poly_sub_loop_inv(f_new: seq<uint256>, f: seq<uint256>, g: seq<uint256>, i: nat)
    {
        reveal contains_elems();
        && contains_elems(f_new)
        && contains_elems(f)
        && contains_elems(g)
        && 0 <= i <= N.full
        && f_new[i..] == f[i..]
        && (forall j :: 0 <= j < i ==> f_new[j] == mqsub(f[j], g[j]))
    }

    lemma poly_sub_loop_correct(f_new: seq<uint256>, f_old: seq<uint256>, f_orig:seq<uint256>, g: seq<uint256>, i: nat)
      requires i < N.full;
      requires poly_sub_loop_inv(f_old, f_orig, g, i)
      requires f_new == f_old[i := mqsub(f_orig[i], g[i])];
      ensures poly_sub_loop_inv(f_new, f_orig, g, i+1);
    {
      assert |f_new| == |f_old|;
      assert (forall j | 0 <= j < |f_new| :: j != i
        ==> f_new[j] == f_old[j] && j == i ==> f_new[j] == mqsub(f_orig[j], g[j]));
    }
}
