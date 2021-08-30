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

    function sub_mod32_update_A(A:int, a:int, n:int) : int64 
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
      x15: uint32,
      x13: uint32)
      requires
        && sub_mod32_loop_inv(iter_a, iter_n, iter_a', A)
        && iter_a.index < |iter_a.buff| // still in bounds after increment
        && x15 == uint32_add(iter_a.buff[i], A.lh)
        && x13 == uint32_sub(x15, iter_n.buff[i])
        && carry_add == uint32_lt(x15, iter_a.buff[i])
        && carry_sub == uint32_lt(x15, x13)
        && A.uh + carry_add
        && iter_a_next == lw_iter_next(iter_a)
        && iter_n_next == lw_iter_next(iter_n)
        && iter_a'_next == sw_iter_next(iter_a', x13)
      ensures
        sub_mod32_loop_inv(lw_iter_next(iter_a), lw_iter_next(iter_n), iter_a', A');

      {
        assume false;
      }

}
