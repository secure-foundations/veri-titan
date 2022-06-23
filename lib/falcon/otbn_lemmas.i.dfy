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

}
