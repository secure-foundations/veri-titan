include "rsa_ops.i.dfy"
include "../../std_lib/src/Collections/Sequences/LittleEndianNat.dfy"

module ge_mod {

import opened bv_ops  
import opened rsa_ops

import opened DivMod
import opened Power
import opened BASE_32_Seq

lemma {:induction A, i} cmp_sufficient_lemma(A: seq<uint32>, B: seq<uint32>, i: nat)
        requires 0 <= i < |A| == |B|;
        requires forall j :: i < j < |A| ==> (A[j] == B[j]);
        ensures A[i] > B[i] ==> (ToNatRight(A) > ToNatRight(B));
        ensures A[i] < B[i] ==> (ToNatRight(A) < ToNatRight(B));
    {
        var n := |A|;
        if n != 0 {
            if i == n - 1 {
                if A[n-1] > B[n-1] {
                  LemmaSeqMswInequality(B, A);
                } else if A[n-1] < B[n-1] {
                  LemmaSeqMswInequality(A, B);
                }
            } else {
                var n := |A|;
                var A' := A[..n-1];
                var B' := B[..n-1];

                calc ==> {
                    A[i] > B[i];
                    {
                      cmp_sufficient_lemma(A', B', i);
                    }
                    ToNatRight(A') > ToNatRight(B');
                    {
                        LemmaSeqPrefix(A, n-1);
                        LemmaSeqPrefix(B, n-1);
                    }
                    ToNatRight(A[..n-1]) > ToNatRight(B[..n-1]);
                    {
                      assert A[n-1] * Pow(BASE(), n-1) == B[n-1] * Pow(BASE(), n-1);
                    }
                    ToNatRight(A[..n-1]) + A[n-1] * Pow(BASE(), n-1) > ToNatRight(B[..n-1]) + B[n-1] * Pow(BASE(), n-1);
                    {
                      assert A[..n-1] + [A[n-1]] == A;
                      assert B[..n-1] + [B[n-1]] == B;
                    }
                    ToNatRight(A[..n-1]) + ToNatRight(A[n-1..]) * Pow(BASE(), n-1) > ToNatRight(B[..n-1]) + ToNatRight(B[n-1..]) * Pow(BASE(), n-1);
                    {
                        LemmaSeqPrefix(A, n-1);
                        LemmaSeqPrefix(B, n-1);
                        assert ToNatRight(A[..n-1]) + ToNatRight(A[n-1..]) * Pow(BASE(), n-1) == ToNatRight(A);
                        assert ToNatRight(B[..n-1]) + ToNatRight(B[n-1..]) * Pow(BASE(), n-1) == ToNatRight(B);
                    }
                    ToNatRight(A) > ToNatRight(B);
                }
                assert A[n-1] > B[n-1] ==> (ToNatRight(A) > ToNatRight(B));

                calc ==> {
                    A[i] < B[i];
                    {
                      cmp_sufficient_lemma(A', B', i);
                    }
                    ToNatRight(A') < ToNatRight(B');
                    {
                        LemmaSeqPrefix(A, n-1);
                        LemmaSeqPrefix(B, n-1);
                    }
                    ToNatRight(A[..n-1]) < ToNatRight(B[..n-1]);
                    {
                      assert A[n-1] * Pow(BASE(), n-1) == B[n-1] * Pow(BASE(), n-1);
                    }
                    ToNatRight(A[..n-1]) + A[n-1] * Pow(BASE(), n-1) < ToNatRight(B[..n-1]) + B[n-1] * Pow(BASE(), n-1);
                    {
                      assert A[..n-1] + [A[n-1]] == A;
                      assert B[..n-1] + [B[n-1]] == B;
                    }
                    ToNatRight(A[..n-1]) + ToNatRight(A[n-1..]) * Pow(BASE(), n-1) < ToNatRight(B[..n-1]) + ToNatRight(B[n-1..]) * Pow(BASE(), n-1);
                    {
                        LemmaSeqPrefix(A, n-1);
                        LemmaSeqPrefix(B, n-1);
                        assert ToNatRight(A[..n-1]) + ToNatRight(A[n-1..]) * Pow(BASE(), n-1) == ToNatRight(A);
                        assert ToNatRight(B[..n-1]) + ToNatRight(B[n-1..]) * Pow(BASE(), n-1) == ToNatRight(B);
                    }
                    ToNatRight(A) < ToNatRight(B);
                }
                assert A[n-1] < B[n-1] ==> (ToNatRight(A) < ToNatRight(B));
            }
        }
    }
        
  method ge_mod(a: seq<uint32>, n: seq<uint32>) returns (b:bool)
    requires |a| == |n| == 384
    ensures (ToNatRight(a) >= ToNatRight(n)) == b
  {
    var i := |a| - 1;

    var cond := 1;
    b := true;
    
    while (cond != 0)
      invariant cond != 0 ==> 0 <= i < |a|
      invariant cond == 0 ==> -1 <= i < |a|-1
      invariant cond == 1 ==> a[i+1..] == n[i+1..]
      invariant !b ==> cond == 0;
      invariant cond == 0 ==> (b ==> a[i+1] > n[i+1]) || (a == n)
      invariant cond == 0 ==> (ToNatRight(a) >= ToNatRight(n)) == b
      decreases i
    {
      var ai := a[i];
      var ni := n[i];

      cmp_sufficient_lemma(a, n, i);

      if ai != ni {
        cond := 0;
      }
      if ai < ni {
        b := false;
      }
      if i == 0 {
        cond := 0;
      }
      i := i - 1;
    }
  }

    predicate ge_mod32_loop_inv(
      iter_a: iter_t,
      iter_n: iter_t,
      cond: uint1,
      b: bool)
    {
      var i := iter_a.index;
      && cond != 0 ==> 0 <= i < |iter_a.buff|
      && cond == 0 ==> -1 <= i < |iter_a.buff|- 1
      && cond == 1 ==> iter_a.buff[i+1..] == iter_n.buff[i+1..]
      && (cond == 0 ==> (b ==> iter_a.buff[i+1] > iter_n.buff[i+1]) || (iter_a.buff == iter_n.buff))
      && cond == 0 ==> (ToNatRight(iter_a.buff) >= ToNatRight(iter_n.buff)) == b
    }

    lemma lemma_ge_mod32_correct(
      iter_a: iter_t,
      iter_n: iter_t,
      iter_a_prev: iter_t,
      iter_n_prev: iter_t,
      cond: uint1,
      b: bool,
      i: int)
      requires
        && ge_mod32_loop_inv(iter_a, iter_n, cond, b)

        && iter_a.index < |iter_a.buff|
        && i == iter_a.index == iter_n.index
        && i > 0

        //&& cond == uint32_lt(0, uint32_xor(x11, x15)) // cond = x12
        && cond == iter_n.index == |iter_n.buff| - 1

        && iter_a_prev == lw_prev_iter(iter_a)
        && iter_n_prev == lw_prev_iter(iter_n)
      ensures
        ge_mod32_loop_inv(iter_a_prev, iter_n_prev, cond, b)
    {

    }

    
}
