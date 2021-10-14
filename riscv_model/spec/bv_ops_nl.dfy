include "bv_ops.dfy"
  
module bv_ops_nl {

    import opened rv_consts
    import opened bv_ops

    import opened Power2
    import opened DivMod
    
    lemma div_bound(x: int, n: nat)
      requires n > 0
      ensures x >= 0 ==> 0 <= x/n <= x
      ensures x < 0 ==> 0 > (x/n) >= x
    {
      if x >= 0 {
        LemmaDivNonincreasingAuto();
        LemmaDivPosIsPosAuto();
      } else {
        assume false;
      }
    }

    /* signed operations */
    function method int32_rs(x: int32, shift: nat) : int32
    {
      x / Pow2(shift)
    }

    // right arithmetic shift
    function method int64_rs(x: int64, shift: nat) : int64
    {
      x / Pow2(shift)
    }

  }
