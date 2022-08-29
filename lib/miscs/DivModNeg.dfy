include "../../std_lib/src/NonlinearArithmetic/DivMod.dfy"
include "../../std_lib/src/NonlinearArithmetic/Internals/DivInternals.dfy"

module DivModNeg {
  
  import opened DivMod
  import opened DivInternals

  lemma LemmaDivNegIsNeg(x:int, d:int)
    requires x < 0
    requires 0 < d
    decreases d - x
    ensures x / d < 0
  {
    calc {
      x / d;
      { LemmaDivIsDivRecursive(x, d); }
      DivRecursive(x, d);
      { reveal DivRecursive(); }
      DivPos(x, d);
      { reveal DivPos(); }
      -1 + DivPos(x + d, d); 
    }

    if x + d < 0 {
      LemmaDivIsDivRecursive(x + d, d); 
      reveal DivRecursive(); 
      LemmaDivNegIsNeg(x + d, d);
    } else {
      assert x + d < d;
      calc { 
        DivPos(x + d, d);
        { LemmaDivIsDivRecursive(x + d, d); reveal DivRecursive(); }
        (x + d) / d;
        { LemmaBasicDiv(d); }
        0;
      }
    }
  }

  lemma LemmaDivPosRecursiveNondecreasing(x:int, d:int) 
    requires x < 0
    requires 0 < d
    decreases d - x
    ensures DivPos(x, d) >= x
  {
    assert DivPos(x, d) == -1 + DivPos(x + d, d) by { reveal DivPos(); }

    if x + d < 0 {
      calc {
        DivPos(x, d);
        ==  { reveal DivPos(); }
        -1 + DivPos(x + d, d);
        >= -1 + x + d;
      }
    } else {
      calc {
        DivPos(x + d, d);
        { LemmaDivIsDivRecursive(x+d, d); reveal DivRecursive(); }
        (x + d) / d;
        >=  { LemmaDivPosIsPos(x + d, d); }
        0;
      }
    }
  }

  lemma LemmaDivNondecreasing(x: int, d: int)
    requires x < 0
    requires 0 < d
    ensures x / d >= x
  {
    calc {
      x / d;
      { LemmaDivIsDivRecursive(x, d); }
      DivRecursive(x, d);
      { reveal DivRecursive(); }
      DivPos(x, d);
      >=  { LemmaDivPosRecursiveNondecreasing(x, d); }
      x;
    }
  }

  lemma LemmaDivBounded(x: int, n: nat)
    requires n > 0
    ensures x >= 0 ==> 0 <= x/n <= x
    ensures x < 0 ==> 0 > (x/n) >= x
  {
    if x >= 0 {
      LemmaDivNonincreasingAuto();
      LemmaDivPosIsPosAuto();
    } else {
      LemmaDivNondecreasing(x, n);
      LemmaDivNegIsNeg(x, n);
    }
  }

}
