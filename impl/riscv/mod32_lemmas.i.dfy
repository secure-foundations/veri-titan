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
    iter_a: iter_t,
    iter_n: iter_t,
    iter_a': iter_t,
    A: int64_view_t)
  {
    && sub_mod32_A_inv(A)
    && var i := iter_a.index;
    && |iter_a.buff| == |iter_n.buff| == |iter_a'.buff|
    && (i == iter_a'.index == iter_n.index)
    && i <= |iter_a.buff|
    && SeqSub(iter_a.buff[..i], iter_n.buff[..i]) == (iter_a'.buff[..i], A_as_carry(A.full))
  }

  lemma lemma_sub_mod32_correct(
    A: int64_view_t,
    iter_a: iter_t, iter_n: iter_t, iter_a': iter_t,
    iter_a_next: iter_t, iter_n_next: iter_t, iter_a'_next: iter_t,
    v0: uint32, v1: uint32,
    lh: uint32, uh: uint32,
    carry_add: int, carry_sub: int,
    x13: uint32,
    i: int)
  returns  (A': int64_view_t)

  requires sub_mod32_loop_inv(iter_a, iter_n, iter_a', A)
  requires iter_a.index < |iter_a.buff|
  requires i == iter_a.index

  requires v0 == uint32_add(A.lh, iter_a.buff[i]);
  requires x13 == uint32_sub(v0, iter_n.buff[i]);

  requires carry_add == uint32_lt(v0, iter_a.buff[i]);
  requires carry_sub == uint32_lt(v0, x13);
  requires v1 == uint32_add(A.uh, carry_add);

  requires lh == uint32_sub(v1, carry_sub);
  requires uh == to_uint32(int32_rs(to_int32(lh), 31));

  requires iter_a_next == lw_next_iter(iter_a)
  requires iter_n_next == lw_next_iter(iter_n)
  requires iter_a'_next == sw_next_iter(iter_a', x13)

  ensures sub_mod32_loop_inv(iter_a_next, iter_n_next, iter_a'_next, A')
  ensures A' == int64_cons(lh, uh, A'.full)
  {
    var a_i := iter_a_next.buff[i];
    var n_i := iter_n_next.buff[i];

    var (zs_next, bin_next) := SeqSub(iter_a_next.buff[..i+1], iter_n_next.buff[..i+1]);
    var (zs, _) := SeqSub(iter_a.buff[..i], iter_n.buff[..i]);
    
    A' := update_A_correct(A, a_i, n_i, v0, v1, lh, uh, carry_add, carry_sub);

    var (z, bout) := uint32_subb(a_i, n_i, A_as_carry(A.full));

    calc {
      zs_next;
      {
        assert(iter_a_next.buff[..i+1][..i] == iter_a.buff[..i]);
        assert(iter_n_next.buff[..i+1][..i] == iter_n.buff[..i]);
        reveal SeqSub();
      }
      zs + [x13];
      iter_a'.buff[..i] + [x13];
      iter_a'_next.buff[..i+1];
    }

    assert bin_next == if a_i >= n_i + A_as_carry(A.full) then 0 else 1 by {
      assert(iter_a_next.buff[..i+1][..i] == iter_a.buff[..i]);
      assert(iter_n_next.buff[..i+1][..i] == iter_n.buff[..i]);
      reveal SeqSub();
    }

    assert bin_next == A_as_carry(A'.full) by {
      sub_mod32_update_A_lemma(A.full, A'.full, a_i, n_i, bin_next);
    }
  }

  lemma sub_mod32_post_lemma(iter_a: iter_t, iter_n: iter_t, iter_a': iter_t, A: int64_view_t)
    requires sub_mod32_loop_inv(iter_a, iter_n, iter_a', A);
    requires iter_a.index == |iter_a.buff|
    ensures to_nat(iter_a'.buff) ==
      to_nat(iter_a.buff) - to_nat(iter_n.buff) + A_as_carry(A.full) * Power.Pow(BASE_32, |iter_a.buff|)
  {
    var i := iter_a.index;
    assert iter_a.buff[..i] == iter_a.buff;
    assert iter_n.buff[..i] == iter_n.buff;
    assert iter_a'.buff[..i] == iter_a'.buff;
    var cout := A_as_carry(A.full);
    assert SeqSub(iter_a.buff, iter_n.buff) == (iter_a'.buff, cout);
    LemmaSeqSub(iter_a.buff, iter_n.buff, iter_a'.buff, cout);
  }

    // predicate ge_mod32_loop_inv(
    //   iter_a: iter_t,
    //   iter_n: iter_t,
    //   cond: uint1,
    //   b: bool)
    // {
    //   var i := iter_a.index;
    //   && cond != 0 ==> 0 <= i < |iter_a.buff|
    //   && cond == 0 ==> -1 <= i < |iter_a.buff|- 1
    //   && cond == 1 ==> iter_a.buff[i+1..] == iter_n.buff[i+1..]
    //   && (cond == 0 ==> (b ==> iter_a.buff[i+1] > iter_n.buff[i+1]) || (iter_a.buff == iter_n.buff))
    //   && cond == 0 ==> (ToNatRight(iter_a.buff) >= ToNatRight(iter_n.buff)) == b
    // }

    // lemma lemma_ge_mod32_correct(
    //   iter_a: iter_t,
    //   iter_n: iter_t,
    //   iter_a_prev: iter_t,
    //   iter_n_prev: iter_t,
    //   cond: uint1,
    //   b: bool,
    //   i: int)
    //   requires
    //     && ge_mod32_loop_inv(iter_a, iter_n, cond, b)

    //     && iter_a.index < |iter_a.buff|
    //     && i == iter_a.index == iter_n.index
    //     && i > 0

    //     //&& cond == uint32_lt(0, uint32_xor(x11, x15)) // cond = x12
    //     && cond == iter_n.index == |iter_n.buff| - 1

    //     && iter_a_prev == lw_prev_iter(iter_a)
    //     && iter_n_prev == lw_prev_iter(iter_n)
    //   ensures
    //     ge_mod32_loop_inv(iter_a_prev, iter_n_prev, cond, b)
    // {
    // }

}
