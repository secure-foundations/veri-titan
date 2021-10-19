include "rsa_ops.i.dfy"
include "mod32_nl_lemmas.i.dfy"

module mod32_lemmas {
  import opened bv_ops
  import opened rsa_ops
  import opened rv_machine

  import opened mod32_nl_lemmas

  import opened BASE_32_Seq
  import Power2
  import Power

  const B  : int := BASE_32;
  const B2 : int := B * B;

  predicate sub_mod32_loop_inv(
    old_a: seq<uint32>,
    n: seq<uint32>,
    a: seq<uint32>,
    i: nat,
    A: int64_view_t)
  {
    && sub_mod32_A_inv(A)
    && |old_a| == |a| == |n|
    && 0 <= i <= |a|
    && old_a[i..] == a[i..]
    && SeqSub(old_a[..i], n[..i]) == (a[..i], A_as_carry(A.full))
  }

  lemma lemma_sub_mod32_correct(
    A: int64_view_t,
    old_a: seq<uint32>, n: seq<uint32>, a: seq<uint32>,
    v0: uint32, v1: uint32,
    lh: uint32, uh: uint32,
    carry_add: int, carry_sub: int,
    x13: uint32,
    i: nat)
  returns  (A': int64_view_t)

  requires sub_mod32_loop_inv(old_a, n, a, i, A)
  requires i < |a|

  requires v0 == uint32_add(A.lh, old_a[i]);
  requires x13 == uint32_sub(v0, n[i]);

  requires carry_add == uint32_lt(v0, old_a[i]);
  requires carry_sub == uint32_lt(v0, x13);
  requires v1 == uint32_add(A.uh, carry_add);

  requires lh == uint32_sub(v1, carry_sub);
  requires uh == to_uint32(int32_rs(to_int32(lh), 31));

  ensures A' == int64_cons(lh, uh, A'.full)
  ensures sub_mod32_loop_inv(old_a, n, a[i := x13], i + 1, A')
  {
    var a_i := old_a[i];
    var n_i := n[i];

    assert a_i == a[i];

    var (zs_next, bin_next) := SeqSub(old_a[..i+1], n[..i+1]);
    var (zs, _) := SeqSub(old_a[..i], n[..i]);

    A' := update_A_correct(A, a_i, n_i, v0, v1, lh, uh, carry_add, carry_sub);
    var (z, bout) := uint32_subb(a_i, n_i, A_as_carry(A.full));

    calc {
      zs_next;
      {
        assert(old_a[..i+1][..i] == old_a[..i]);
        assert(n[..i+1][..i] == n[..i]);
        reveal SeqSub();
      }
      zs + [x13];
      {
        assert zs == a[..i];
      }
      a[..i] + [x13];
      a[i := x13][..i+1];
    }

    assert bin_next == if a_i >= n_i + A_as_carry(A.full) then 0 else 1 by {
      assert(old_a[..i+1][..i] == old_a[..i]);
      assert(n[..i+1][..i] == n[..i]);
      reveal SeqSub();
    }

    assert bin_next == A_as_carry(A'.full) by {
      sub_mod32_update_A_lemma(A.full, A'.full, a_i, n_i, bin_next);
    }
  }

  lemma sub_mod32_post_lemma(old_a: seq<uint32>, n: seq<uint32>, a: seq<uint32>, A: int64_view_t)
    requires sub_mod32_loop_inv(old_a, n, a, |a|, A);
    ensures to_nat(a) ==
      to_nat(old_a) - to_nat(n) + A_as_carry(A.full) * Power.Pow(BASE_32, |old_a|)
  {
    var i := |old_a|;
    assert old_a[..i] == old_a;
    assert n[..i] == n;
    assert a[..i] == a;
    var cout := A_as_carry(A.full);
    assert SeqSub(old_a, n) == (a, cout);
    LemmaSeqSub(old_a, n, a, cout);
  }

    // predicate ge_mod32_loop_inv(
    //   old_a: iter_t,
    //   n: iter_t,
    //   cond: uint1,
    //   b: bool)
    // {
    //   var i := old_a.index;
    //   && cond != 0 ==> 0 <= i < |old_a|
    //   && cond == 0 ==> -1 <= i < |old_a|- 1
    //   && cond == 1 ==> old_a[i+1..] == n[i+1..]
    //   && (cond == 0 ==> (b ==> old_a[i+1] > n[i+1]) || (old_a == n))
    //   && cond == 0 ==> (ToNatRight(old_a) >= ToNatRight(n)) == b
    // }

    // lemma lemma_ge_mod32_correct(
    //   old_a: iter_t,
    //   n: iter_t,
    //   old_a_prev: iter_t,
    //   n_prev: iter_t,
    //   cond: uint1,
    //   b: bool,
    //   i: int)
    //   requires
    //     && ge_mod32_loop_inv(old_a, n, cond, b)

    //     && old_a.index < |old_a|
    //     && i == old_a.index == n.index
    //     && i > 0

    //     //&& cond == uint32_lt(0, uint32_xor(x11, x15)) // cond = x12
    //     && cond == n.index == |n| - 1

    //     && old_a_prev == lw_prev_iter(old_a)
    //     && n_prev == lw_prev_iter(n)
    //   ensures
    //     ge_mod32_loop_inv(old_a_prev, n_prev, cond, b)
    // {
    // }

}
