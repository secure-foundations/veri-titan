include "../spec/bv_ops.dfy"
include "../spec/rsa_ops.dfy"
include "../lib/powers.dfy"
include "../../libraries/src/Collections/Sequences/LittleEndianNat.dfy"

module ge_mod {

import opened powers
import opened bv_ops  
import opened rv_consts
import opened rsa_ops

import opened DivMod
import opened Power
import opened BoundedInts
import opened BASE_32_Seq
// 
// function interp(A: seq<uint32>, n: nat) : nat
//     decreases n;
//     requires 0 <= n <= |A|;
// {
//     if n == 0 then 0
//     else word_interp(A, n - 1) + interp(A, n - 1)
// }
// 
// lemma {:induction i} prefix_sum_lemma(S: seq<uint32>, S': seq<uint32>, i: nat)
//     requires 0 <= i <= |S| && 0 <= i <= |S'|;
//     requires S[..i] == S'[..i];
//     ensures interp(S, i) == interp(S', i);
// {
//     assert true;
// }
//         
// function word_interp(A: seq<uint32>, i: nat) : nat
//     requires i < |A|;
// {
//     A[i] as nat * postional_weight(i)
// }
// 
// function postional_weight(i: nat) : nat
// {
//     power(BASE_32, i) as nat
// }
// 
// lemma {:induction A} ToNatRight_upper_bound_lemma(A: seq<uint32>, n: nat)
//     requires |A| == n;
//     ensures ToNatRight(A) < pow_B32(|A|);
// {
//     if |A| == 0 {
//         reveal power();
//     } else {
//         ghost var A' := A[..(|A| - 1)];
// 
//         calc ==> {
//             ToNatRight(A) == word_interp(A, |A| - 1) + interp(A, |A| - 1);
//             {
//                 assert ToNatRight(A') == interp(A, |A| - 1) by {
//                     prefix_sum_lemma(A, A', |A| - 1);
//                 }   
//             }
//             ToNatRight(A) == word_interp(A, |A| - 1) + ToNatRight(A');
//             {
//                 assert ToNatRight(A') < power(BASE_32, |A'|) by {
//                     ToNatRight_upper_bound_lemma(A', |A'|);
//                 }
//             }
//             ToNatRight(A) < word_interp(A, |A| - 1) + power(BASE_32, |A'|);
//             {
//                 assert word_interp(A, |A| - 1) <= power(BASE_32, |A|) - power(BASE_32, |A| - 1) by {
//                     word_interp_upper_bound_lemma(A, |A| - 1);
//                 }
//             }
//             ToNatRight(A) < power(BASE_32, |A|) - power(BASE_32, |A| - 1) + power(BASE_32, |A'|);
//             ToNatRight(A) < power(BASE_32, |A|);
//         }
//     }
// }
// 
// lemma {:induction i} word_interp_upper_bound_lemma(A: seq<uint32>, i: nat)
//     requires i < |A|;
//     ensures word_interp(A, i) <= power(BASE_32, i + 1) - power(BASE_32, i);
// {
//     assert A[i] as int <= BASE_32;
//     calc ==> {
//         A[i] as int <= BASE_32;
//         A[i] as int * postional_weight(i) <= (BASE_32 - 1) * postional_weight(i);
//         {
//             assert word_interp(A, i) == A[i] as int * postional_weight(i);
//         }
//          word_interp(A, i) <= (BASE_32 - 1) * postional_weight(i);
//          word_interp(A, i) <= (BASE_32 - 1) * power(BASE_32, i);
//          word_interp(A, i) <= BASE_32 * power(BASE_32, i) - power(BASE_32, i);
//          {
//             power_add_one_lemma(BASE_32, i);
//          }
//          word_interp(A, i) <= power(BASE_32, i + 1) - power(BASE_32, i);
//     }
// }
// 
// lemma cmp_msw_lemma(A: seq<uint32>, B: seq<uint32>)
//     requires |A| == |B| != 0;
//     ensures A[|A| - 1] > B[|B| - 1] ==> (ToNatRight(A) > ToNatRight(B));
//     ensures A[|A| - 1] < B[|B| - 1] ==> (ToNatRight(A) < ToNatRight(B));
// {
//     var n := |A|;
//     var A' := A[..n-1];
//     var B' := B[..n-1];
//     calc == {
//         ToNatRight(A) - ToNatRight(B);
//         {
//             prefix_sum_lemma(A, A', n - 1);
//             prefix_sum_lemma(B, B', n - 1);
//         }
//         interp(A', n - 1) +  word_interp(A, n - 1) - interp(B', n - 1) - word_interp(B, n - 1);
//         ToNatRight(A') - ToNatRight(B') + word_interp(A, n - 1) - word_interp(B, n - 1);
//         ToNatRight(A') - ToNatRight(B') + (A[n - 1] as int - B[n - 1] as int)  * postional_weight(n - 1);
//     }
// 
//     if A[n - 1] > B[n - 1] {
//         calc >= {
//             ToNatRight(A') - ToNatRight(B') + (A[n - 1] as int - B[n - 1] as int)  * postional_weight(n - 1);
//             {
//                 assert (A[n - 1] as int - B[n - 1] as int) >= 1;
//             }
//             ToNatRight(A') - ToNatRight(B') + postional_weight(n - 1);
//             {
//                 assert ToNatRight(A') >= 0;
//             }
//             postional_weight(n - 1) - ToNatRight(B');
//             power(BASE_32, n - 1) - ToNatRight(B');
//         }
// 
//         assert ToNatRight(B') < power(BASE_32, n - 1) by {
//             ToNatRight_upper_bound_lemma(B', n-1);
//         }
// 
//         assert power(BASE_32, n - 1) - ToNatRight(B') > 0;
//         assert ToNatRight(A) > ToNatRight(B);
//     } else if A[n - 1] < B[n - 1] {
//         calc <= {
//             ToNatRight(A') - ToNatRight(B') + (A[n - 1] as int - B[n - 1] as int)  * postional_weight(n - 1);
//             {
//                 assert (B[n - 1] as int - A[n - 1] as int) >= 1;
//             }
//             ToNatRight(A') - ToNatRight(B') - postional_weight(n - 1);
//             {
//                 assert ToNatRight(B') >= 0;
//             }
//             ToNatRight(A') - postional_weight(n - 1);
//             ToNatRight(A') - power(BASE_32, n - 1);
//         }
// 
//         assert ToNatRight(A') < power(BASE_32, n - 1) by {
//             ToNatRight_upper_bound_lemma(A', n-1);
//         }
// 
//         assert ToNatRight(A') - power(BASE_32, n - 1) < 0;
//         assert ToNatRight(A) < ToNatRight(B);
//     }
// }
// 
// lemma {:induction A, i} cmp_sufficient_lemma(A: seq<uint32>, B: seq<uint32>, i: nat)
//         requires 0 <= i < |A| == |B|;
//         requires forall j :: i < j < |A| ==> (A[j] == B[j]);
//         ensures A[i] > B[i] ==> (ToNatRight(A) > ToNatRight(B));
//         ensures A[i] < B[i] ==> (ToNatRight(A) < ToNatRight(B));
//     {
//         var n := |A|;
//         if n != 0 {
//             if i == n - 1 {
//                 cmp_msw_lemma(A, B);
//             } else {
//                 var n := |A|;
//                 var A' := A[..n-1];
//                 var B' := B[..n-1];
// 
//                 calc ==> {
//                     A[i] > B[i];
//                     {
//                         cmp_sufficient_lemma(A', B', i);
//                     }
//                     ToNatRight(A') > ToNatRight(B');
//                     {
//                         prefix_sum_lemma(A, A', n - 1);
//                         prefix_sum_lemma(B, B', n - 1);
//                     }
//                     interp(A, n - 1) > interp(B, n - 1);
//                     {
//                         assert word_interp(A, n - 1) == word_interp(B, n - 1);
//                     }
//                     interp(A, n - 1) +  word_interp(A, n - 1) > interp(B, n - 1) + word_interp(B, n - 1);
//                     ToNatRight(A) > ToNatRight(B);
//                 }
//                 assert A[i] > B[i] ==> (ToNatRight(A) > ToNatRight(B));
// 
//                 calc ==> {
//                     A[i] < B[i];
//                     {
//                         cmp_sufficient_lemma(A', B', i);
//                     }
//                     ToNatRight(A') < ToNatRight(B');
//                     {
//                         prefix_sum_lemma(A, A', n - 1);
//                         prefix_sum_lemma(B, B', n - 1);
//                     }
//                     interp(A, n - 1) < interp(B, n - 1);
//                     {
//                         assert word_interp(A, n - 1) == word_interp(B, n - 1);
//                     }
//                     interp(A, n - 1) +  word_interp(A, n - 1) < interp(B, n - 1) + word_interp(B, n - 1);
//                     ToNatRight(A) < ToNatRight(B);
//                 }
//                 assert A[i] < B[i] ==> (ToNatRight(A) < ToNatRight(B));
//             }
//         }
//     }

        
lemma ge_to_nat(a: seq<uint32>, n: seq<uint32>, i: nat)
  requires |a| == |n|
  requires i < |a|
  requires a[i] < n[i]
  requires forall j :: i < j < |a| ==> a[j] == n[j]
  ensures ToNatRight(a) < ToNatRight(n)
{
  // cmp_sufficient_lemma(a, n, i);
  LemmaSeqMswInequality(a, n);
  calc {
    ToNatRight(a[..i] + [a[i]] + a[i+1..]) < ToNatRight(n[..i] + [n[i]] + n[i+1..]);
    { assert a[..i] + [a[i]] + a[i+1..] == a;
      assert n[..i] + [n[i]] + n[i+1..] == n;
    }
    ToNatRight(a) < ToNatRight(n);
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
    
}
