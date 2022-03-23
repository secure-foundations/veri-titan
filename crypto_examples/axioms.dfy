include "pow2.dfy"
import opened Power
import opened DivMod
import opened pows_of_2

const G: nat := 7 // 256-th root of unity
const Q: nat := 12289


// NOTE: Needs to run with `/arith:0`


lemma Gpowers() 
  ensures Pow(G, Pow2(7)) == 1487815647197611695910312681741273570332356717154798949898498305086387315423300999654757561928633305897036801;
  ensures Pow(G, Pow2(8)) == 
    2213595400046048155450188615474945937162517050260073069916366390524704974007989996848003433837940380782794455262312607598867363425940560014856027866381946458951205837379116473663246733509680721264246243189632348313601;
/*
{
  calc {
    Pow(G, Pow2(8));
      { reveal Pow(); assert Pow2(8) == 256; }
    Pow(G, 256);
      { LemmaPowAdds(G,128,128); }
    Pow(G, 128) * Pow(G, 128);
      { LemmaPowAdds(G,64,64); }
    Pow(G, 64) * Pow(G, 64) * Pow(G, 64) * Pow(G, 64);
      { LemmaPowAdds(G,32,32); }
    Pow(G, 32) * Pow(G, 32) * Pow(G, 32) * Pow(G, 32) * Pow(G, 32) * Pow(G, 32) * Pow(G, 32) * Pow(G, 32);
      { LemmaPowAdds(G,16,16); }
    Pow(G, 16) * Pow(G, 16) * Pow(G, 16) * Pow(G, 16) * Pow(G, 16) * Pow(G, 16) * Pow(G, 16) * Pow(G, 16) * Pow(G, 16) * Pow(G, 16) * Pow(G, 16) * Pow(G, 16) * Pow(G, 16) * Pow(G, 16) * Pow(G, 16) * Pow(G, 16);
      { assert Pow(G, 16) == 33232930569601 by { reveal Pow(); } }
    33232930569601 * 33232930569601 * 33232930569601 * 33232930569601 * 33232930569601 * 33232930569601 * 33232930569601 * 33232930569601 * 33232930569601 * 33232930569601 * 33232930569601 * 33232930569601 * 33232930569601 * 33232930569601 * 33232930569601 * 33232930569601;
    2213595400046048155450188615474945937162517050260073069916366390524704974007989996848003433837940380782794455262312607598867363425940560014856027866381946458951205837379116473663246733509680721264246243189632348313601;
  }
  
//  
//  calc {
//    Pow(G, Pow2(8));
//    Pow(G, 2*Pow2(7));
//  }
// TODO:
  assume Pow(G, Pow2(7)) == 1487815647197611695910312681741273570332356717154798949898498305086387315423300999654757561928633305897036801;
}

lemma nth_root_lemma()
    ensures Pow(G, Pow2(11)) % Q == 1;
{
  Gpowers();
  calc {
    Pow(G, Pow2(11)) % Q;
      { LemmaPowAdds(2,3,8); }
    Pow(G, Pow2(3) * Pow2(8)) % Q;
    Pow(G, Pow2(8) * Pow2(3)) % Q;
      { LemmaPowMultiplies(G, Pow2(8), Pow2(3)); }
    Pow(Pow(G, Pow2(8)), Pow2(3)) % Q;
      { LemmaPowModNoop(Pow(G, Pow2(8)), Pow2(3), Q); }
    Pow(Pow(G, Pow2(8)) % Q, Pow2(3)) % Q;
    Pow(7143, Pow2(3)) % Q;
      { reveal Pow(); assert Pow2(3) == 8; }
    Pow(7143, 8) % Q;
      { reveal Pow(); }
    1;
  }
}
*/
    type elem = i :nat | i < Q
    function method omega_n(n: pow2_t): elem
        requires n.exp <= 8
    {
        Pow(G, Pow2(8 - n.exp)) % Q
    }

    function method omega_nk(n: pow2_t, k: nat): elem
        requires n.exp <= 8
    {
        Pow(omega_n(n), k) % Q
    }
/*
lemma ntt_cancellation_lemma(n: pow2_t, k: nat)
    requires n.exp != 0
    requires n.exp <= 8
    ensures omega_nk(pow2_half(n), k) == omega_nk(n, 2 * k)
{
  calc {
    omega_nk(pow2_half(n), k);
    Pow(omega_n(pow2_half(n)), k) % Q;
    Pow(Pow(G, Pow2(8 - pow2_half(n).exp)) % Q, k) % Q;
    Pow(Pow(G, Pow2(8 - (n.exp - 1))) % Q, k) % Q;
    Pow(Pow(G, Pow2(8 - n.exp + 1)) % Q, k) % Q;
      { LemmaPowModNoop(Pow(G, Pow2(8 - n.exp + 1)), k, Q); }
    Pow(Pow(G, Pow2(8 - n.exp + 1)), k) % Q;
      calc {
        Pow2(8 - n.exp + 1);
          reveal Pow();
        Pow2(8 - n.exp)*2;
      }
    Pow(Pow(G, Pow2(8 - n.exp)*2), k) % Q;
      { LemmaPowMultiplies(G, Pow2(8 - n.exp), 2); }
    Pow(Pow(Pow(G, Pow2(8 - n.exp)), 2), k) % Q;
      { LemmaPowMultiplies(Pow(G, Pow2(8 - n.exp)), 2, k); } 
    Pow(Pow(G, Pow2(8 - n.exp)), 2*k) % Q;
      { LemmaPowModNoop(Pow(G, Pow2(8 - n.exp)), 2*k, Q); }
    Pow(Pow(G, Pow2(8 - n.exp)) % Q, 2*k) % Q;
    Pow(omega_n(n), 2*k) % Q;
    omega_nk(n, 2 * k);
  }
}
*/
lemma ntt_halving_lemma(n: pow2_t, k: nat)
    requires 1 <= n.exp <= 8
    ensures omega_nk(n, 2 * k + n.full)
            ==
        omega_nk(n, 2 * k);

lemma ntt_neg_one_lemma(n: pow2_t)
    requires n.exp <= 8;
    requires n.full % 2 == 0;
    //ensures omega_nk(n, n.full / 2) == Q - 1;
{
  assume n.exp >= 1;
  var k := n.full / 2;
  assert n.full == 2 * k by { LemmaFundamentalDivMod(n.full, 2); }

  assert n.full == Pow2(n.exp);

//  calc {
//    2 * k;
//      { reveal Pow(); }
//    Pow2(1) * k;
//    Pow2(n.exp);
//  }

//  calc {
//    Pow2(1) * k * Pow2(-1);
//    Pow2(1) * Pow2(-1) * k; 
//      { LemmaPowAddsAuto(); }
//    Pow2(1 + (-1)) * k; 
//    Pow2(n.exp);
//    
//  }

  LemmaPow1(2);
  calc {
    k;
    n.full/2;
    Pow2(n.exp) / 2;
    Pow2(n.exp) / Pow2(1);
      { LemmaPowSubtracts(2, 1, n.exp); }
    Pow2(n.exp - 1);
  }


  calc {
    omega_nk(n, n.full / 2);
    omega_nk(n, k);
    Pow(omega_n(n), k) % Q;
    Pow(Pow(G, Pow2(8 - n.exp)) % Q, k) % Q;
      { LemmaPowModNoop(Pow(G, Pow2(8 - n.exp)), k, Q); }
    Pow(Pow(G, Pow2(8 - n.exp)), k) % Q;
      { LemmaPowMultiplies(G, Pow2(8 - n.exp), k); }
    Pow(G, Pow2(8 - n.exp) * k) % Q;
    Pow(G, Pow2(8 - n.exp) * Pow2(n.exp - 1)) % Q;
      { LemmaPowAdds(2, 8 - n.exp, n.exp - 1); }
    Pow(G, Pow2(8 - n.exp + n.exp - 1)) % Q;
    Pow(G, Pow2(7)) % Q;
      { reveal Pow();  assert Pow2(7) == 128; }
    Pow(G, 128) % Q;
//      { Gpowers(); }
//    Q - 1;
  }
    

//  calc {
//    omega_nk(n, n.full);
//    omega_nk(n, 2*k);
//      { ntt_halving_lemma(n, k); }
//    omega_nk(n, 2*k + n.full);
//    omega_nk(n, n.full + n.full);
//
//  }
//
//  p^n == p^{2n} % Q
//  p^n == p^{2n} % Q
//  p ^ {2n} - p^n == 0 % Q
//  p ^ {n} * (p ^ {n} - 1) == 0 % Q
}
