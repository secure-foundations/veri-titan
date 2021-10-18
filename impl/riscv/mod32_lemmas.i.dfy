include "rsa_ops.i.dfy"
include "mod32_nl_lemmas.i.dfy"

module mod32_lemmas {
  import opened bv_ops
  import opened rsa_ops
  import opened rv_machine

  import opened mod32_nl_lemmas

  import opened BASE_32_Seq
  import Power2

  const B  : int := BASE_32;
  const B2 : int := B * B;

  predicate sub_mod32_loop_inv(
    iter_a: iter_t,
    iter_n: iter_t,
    iter_a': iter_t,
    A: int64_view_t)
  {
    && (A.full == 0 || A.full == -1)
    && ((A.lh == A.uh == 0) || (A.lh == A.uh == 0xffff_ffff))
    && var i := iter_a.index;
    && |iter_a.buff| == |iter_n.buff| == |iter_a'.buff|
    && (i == iter_a'.index == iter_n.index)
    && i <= |iter_a.buff|
    && SeqSub(iter_a.buff[..i], iter_n.buff[..i]) == (iter_a'.buff[..i], neg1_to_uint1(A.full))
  }

  lemma lemma_sub_mod32_correct(
    A: int64_view_t,
    iter_a: iter_t, iter_n: iter_t, iter_a': iter_t,
    iter_a_next: iter_t, iter_n_next: iter_t, iter_a'_next: iter_t,
    v0: uint32, v1: uint32,
    lh: uint32, uh: uint32,
    carry_add: int, carry_sub: int,
    x12: uint32, x13: uint32,
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
    {
      var a_i := iter_a_next.buff[i];
      var n_i := iter_n_next.buff[i];

      var (zs_next, bin_next) := SeqSub(iter_a_next.buff[..i+1], iter_n_next.buff[..i+1]);
      var (zs, _) := SeqSub(iter_a.buff[..i], iter_n.buff[..i]);

      A' := update_A_correct(A, a_i, n_i, v0, v1, uh, lh, carry_add, carry_sub);
      assume (A.full == A.lh == A.uh == 0) || (A.full == -1 <==> (A.lh == A.uh == 0xffff_ffff));

      var (z, bout) := uint32_subb(a_i, n_i, neg1_to_uint1(A.full));

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

      assert bin_next == if a_i >= n_i + neg1_to_uint1(A.full) then 0 else 1 by {
        assert(iter_a_next.buff[..i+1][..i] == iter_a.buff[..i]);
        assert(iter_n_next.buff[..i+1][..i] == iter_n.buff[..i]);
        reveal SeqSub();
      }

      assert bin_next == neg1_to_uint1(A'.full) by {
        sub_mod32_update_A_lemma(A.full, A'.full, a_i, n_i, bin_next);
      }
    }
  
/*
  lemma lemma_sub_mod32_A_inv(
    A: int64_view_t, // old A
    A': int64_view_t, // new A
    a_i: uint32,
    x13: uint32,
    carry_add: int,
    carry_sub: int)
    requires A.full == 0 || A.full == -1
    requires carry_add == uint32_lt(uint32_add(A.lh, a_i), a_i) 
    requires carry_sub == uint32_lt(uint32_add(A.lh, a_i), x13) 
    requires A'.lh == uint32_sub(uint32_add(carry_add, A.uh), carry_sub) 
    requires A'.uh == to_uint32(int32_rs(to_int32(A'.lh), 31))
    ensures A'.full == 0 || A'.full == -1;
    ensures A'.lh == 0 ==> A'.full == 0;
    ensures A'.lh == 0xffff_ffff ==> A'.full == -1;
  {
    var v1 := uint32_add(A.uh, carry_add);
    var v2 := uint32_sub(v1, carry_sub);

    if A.full == 0 {
      assert A.uh == 0 && A.lh == 0 by {
        lemma_int64_half_split(A);
      }
      assert carry_sub == 1 ==> v2 == 0xffff_ffff;
      assert carry_sub == 0 ==> v2 == 0;
    } else {
      assert A.uh == 0xffff_ffff && A.lh == 0xffff_ffff by {
        lemma_int64_half_split(A);
      }
      assert carry_add == 1 ==> A'.lh == uint32_sub(0, carry_sub);
      assert carry_add == 0 ==> A'.lh == uint32_sub(0xffff_ffff, carry_sub);
    }

    assert A'.lh == 0xffff_ffff || A'.lh == 0;

    uinteresting(A'.lh, A'.uh);

    if A'.lh == 0 {
      assert A'.uh == 0;
      lemma_int64_half_split(A');
      assert A'.full == 0;
    } else {
      assert A'.lh == 0xffff_ffff;
      assert A'.uh == 0xffff_ffff;
      lemma_int64_negative_one(A');
      assert A'.full == -1;
    }
  }
*/

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
