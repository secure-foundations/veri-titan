include "../../arch/otbn/machine.s.dfy"
include "../../arch/otbn/vale.i.dfy"
include "ntt_params.dfy"

module otbn_lemmas {
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul
    import opened integers
    import opened bv32_ops
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


    lemma lemma_small_mulqacc(x: uint256, y: uint256, r: uint256, old_wacc: uint256, old_flags: flags_t)
      requires x < BASE_64 && y < BASE_64
      requires var product := otbn_mulqacc(true, x, 0, y, 0, 0, old_wacc);
               r == otbn_mulqacc_so(product, 0, true, old_flags).new_dst
      ensures r == x * y

    lemma lemma_montymul_correct(x: uint256, y: uint256, prod: uint256, sum: uint256, diff1: uint256, flags: flags_t, diff2: uint256)
      requires 0 <= x * y < BASE_64
      requires prod == (x * y) * (Q * (Q-2))
      requires sum == otbn_addc(prod, x*y, SFT(false, 2), false).0;
      requires diff1 == otbn_subb(sum, Q, SFT_DFT, false).0;
      requires flags == otbn_subb(sum, Q, SFT_DFT, false).1;
      requires diff2 == otbn_subb(diff1, if flags.get_single_flag(0) then 0 else Q, SFT_DFT, false).0;
      ensures IsModEquivalent(diff2 * 4091, x * y, 12289);
}
