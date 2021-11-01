include "rsa_ops.i.dfy"

module mont_mul_add_lemmas {
  import opened bv_ops
  import opened rsa_ops
  import opened rv_machine

  import opened BASE_32_Seq
  import Power2
  import Power

  lemma refine_uint64_view(lh: uint32, uh: uint32, full: uint64) returns (r: uint64_view_t)
    requires lh == uint64_lh(full);
    requires uh == uint64_uh(full);
    ensures valid_uint64_view(r, lh, uh)
  {
    r := uint64_cons(lh, uh, full);
    lemma_uint64_half_split(r.full);
    assert valid_uint64_view(r, lh, uh);
  }
  
  lemma uint64_view_zero() returns (r: uint64_view_t)
    ensures r == uint64_cons(0, 0, 0);
  {
    reveal uint64_lh();
    reveal uint64_uh();
    r := refine_uint64_view(0, 0, 0);
  }
  
  predicate mont_mul_add_loop_inv(
    A: uint64_view_t,
    B: uint64_view_t,
    A_prev: uint64_view_t,
    B_prev: uint64_view_t,
    n: seq<uint32>,
    b: seq<uint32>,
    c: seq<uint32>,
    a: uint32,
    d0: uint32,
    i: nat)
  {
    && |n| == |b| == |c|
    && 0 <= i < |n|

    && A.full == a * b[i] + c[i] + A_prev.uh
    && B.full == d0 * n[i] + A.lh + B_prev.uh
    && (i > 0 ==> c[i-1] == B.lh)
  }

}
