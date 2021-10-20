include "rsa_ops.i.dfy"
include "../../std_lib/src/Collections/Sequences/LittleEndianNat.dfy"

module ge_mod_lemmas {

import opened bv_ops  
import opened rsa_ops
import opened rv_machine

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

  function method uint32_to_bool(x: uint32) : bool
  requires x == 0 || x == 1;
  {
    if x == 0 then false else true
  }

  function method uint32_to_uint1(x: uint32) : uint1
  requires x == 0 || x == 1;
  {
    if x == 0 then 0 else 1
  }

  predicate ge_mod32_loop_inv(
    old_a: iter_t,
    n: iter_t,
    cond: uint1,
    b: bool)
  {
    var i := old_a.index;
    && cond != 0 ==> 0 <= i < |old_a.buff|
    && cond == 0 ==> -1 <= i < |old_a.buff|- 1
    && cond == 1 ==> old_a.buff[i+1..] == n.buff[i+1..]
    && (cond == 0 ==> (b ==> old_a.buff[i+1] > n.buff[i+1]) || (old_a.buff == n.buff))
    && cond == 0 ==> (ToNatRight(old_a.buff) >= ToNatRight(n.buff)) == b
  }

  lemma lemma_ge_mod32_correct(
    old_a: iter_t,
    n: iter_t,
    old_a_prev: iter_t,
    n_prev: iter_t,
    cond: uint1, // uint1
    b: bool, // bool
    i: int)
    requires
      && ge_mod32_loop_inv(old_a, n, cond, b)

      && old_a.index < |old_a.buff|
      && i == old_a.index == n.index
      && i > 0

      && cond == n.index == |n.buff| - 1

      && old_a_prev == lw_prev_iter(old_a)
      && n_prev == lw_prev_iter(n)
    ensures
      ge_mod32_loop_inv(old_a_prev, n_prev, cond, b)
  {
  }

}
