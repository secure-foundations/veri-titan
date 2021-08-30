include "../spec/rsa_ops.dfy"

module mod32_lemmas {
  
    import opened bv_ops
    import opened rv_ops
    import opened rsa_ops
    import opened rv_consts
    import opened powers
    import opened congruences

    const B  : int := BASE_32;
    const B2 : int := B * B;

    function sub_mod32_update_A(A:int64, a:int, n:int) : int64 
      requires
      && (0 <= a < BASE_32)
      && (n <= 0 < BASE_32)
    {
      to_int64(A + a - n)
    }

    predicate sub_mod32_loop_inv(
      iter_a: iter_t,
      iter_n: iter_t,
      iter_a': iter_t,
      A: int64)
    {
      && (A == 0 || A == -1)
      && var i := iter_a.index;
      && |iter_a.buff| == |iter_n.buff| == |iter_a'.buff|
      && (i == iter_a'.index == iter_n.index)
      && i <= |iter_a.buff|
      && seq_subb(iter_a.buff[..i], iter_n.buff[..i]) == (iter_a'.buff[..i], neg1_to_uint1(A))
    }

    lemma lemma_sub_mod32_correct(
      A: int64_view_t, // old A
      A': int64_view_t, // new A
      iter_a: iter_t,
      iter_n: iter_t,
      iter_a': iter_t,
      iter_a_next: iter_t,
      iter_n_next: iter_t,
      iter_a'_next: iter_t,
      x13: uint32,
      x14: uint32,
      i: int)
      requires
        && sub_mod32_loop_inv(iter_a, iter_n, iter_a', A.full)
        && iter_a.index < |iter_a.buff| // still in bounds after increment
        && i == iter_a.index
        && A'.lh == uint32_add(iter_a.buff[i], A.lh)
        && x13 == uint32_sub(A'.lh, iter_n.buff[i])
        && A.uh + uint32_lt(A'.lh, iter_a.buff[i]) == x14
        && iter_a_next == lw_next_iter(iter_a)
        && iter_n_next == lw_next_iter(iter_n)
        && iter_a'_next == sw_next_iter(iter_a', x13)
      ensures
        sub_mod32_loop_inv(lw_next_iter(iter_a), lw_next_iter(iter_n), iter_a', A'.full)

      {
        var carry_add := uint32_lt(A'.lh, iter_a.buff[i]);
        var carry_sub := uint32_lt(A.lh, x13);
        assume false;
      }

}
