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

    lemma sub_mod32_A_bound_lemma(A:int, a:int, n:int)
      requires
      && (A == 0 || A == -1)
      && (0 <= a < BASE_32)
      && (0 <= n < BASE_32)
      ensures
      -BASE_63 <= (A + a - n) <= BASE_63 - 1
    {
      calc {
        A + a;
        <= BASE_32;
        < BASE_63 - 1;
      }
      calc {
        (BASE_63 - 1) - n;
        >= (BASE_63 - 1) - BASE_32;
        >= -BASE_63;
      }
    }
    
    function sub_mod32_update_A(A:int64, a:int, n:int) : int64 
      requires
      && (A == 0 || A == -1)
      && (0 <= a < BASE_32)
      && (0 <= n < BASE_32)
    {
      sub_mod32_A_bound_lemma(A, a, n);
      A + a - n
    }

    predicate sub_mod32_loop_inv(
      iter_a: iter_t,
      iter_n: iter_t,
      iter_a': iter_t,
      A: int64)
    {
      && (A == 0 || A == -1)
      && var i := iter_a.index; // automatic
      && |iter_a.buff| == |iter_n.buff| == |iter_a'.buff| // invariant
      && (i == iter_a'.index == iter_n.index)
      && i <= |iter_a.buff| // prove?
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
      carry_add: int,
      carry_sub: int,
      x13: uint32, //saved partial A'
      x14: uint32,
      i: int)
      requires
        && sub_mod32_loop_inv(iter_a, iter_n, iter_a', A.full)
        && iter_a.index < |iter_a.buff| // still in bounds after increment
        
        && i == iter_a.index

        // x13 == A.lh + a[i] - n[i]
        && x13 == uint32_sub(uint32_add(A.lh, iter_a.buff[i]), iter_n.buff[i])
        
        && carry_add == uint32_lt(uint32_add(A.lh, iter_a.buff[i]), iter_a.buff[i]) // overflow bit
        && carry_sub == uint32_lt(uint32_add(A.lh, iter_a.buff[i]), x13) // underflow bit
        
        && A'.lh == uint32_sub(uint32_add(carry_add, A.uh), carry_sub) // either 0 or -1
        && A'.uh == uint32_rs(A'.lh, 31) // just a sign value
        && A'.full == int64_rs(sub_mod32_update_A(A.full, iter_a.buff[i], iter_n.buff[i]), 32)
        
        && iter_a_next == lw_next_iter(iter_a)
        && iter_n_next == lw_next_iter(iter_n)
        && iter_a'_next == sw_next_iter(iter_a', x13)
      ensures
        sub_mod32_loop_inv(iter_a_next, iter_n_next, iter_a'_next, A'.full)

      {
        var A'_uh := A'.uh;
        var A'_lh := A'.lh;
        var A'_full := A'.full as int;

        var ca_plus_Auh := uint32_add(A.uh, carry_add);
        var ca_plus_Auh_minus_cs := uint32_sub(ca_plus_Auh, carry_sub);

        if A.full == 0 {
          assert(A.uh == 0 && A.lh == 0)
            by { lemma_int64_half_split(A.full); }
          assert(ca_plus_Auh == 0);
          assert(ca_plus_Auh_minus_cs == 0xffff_ffff || ca_plus_Auh_minus_cs == 0)
            by { reveal_uint32_sub(); lemma_int64_half_split(A.full); }
          assert(A'.lh == ca_plus_Auh_minus_cs);
        }
        else {
          assert(A.uh == 0xffff_ffff && A.lh == 0xffff_ffff)
            by { lemma_int64_half_split(A.full); }
          assert(ca_plus_Auh == 0xffff_ffff || ca_plus_Auh == 0);
          assert(ca_plus_Auh_minus_cs == 0xffff_ffff || ca_plus_Auh_minus_cs == 0)
            by { reveal_uint32_sub(); }
        }

        var (zs_next, bin_next) := seq_subb(iter_a_next.buff[..i+1], iter_n_next.buff[..i+1]);
        var (zs, bin) := seq_subb(iter_a.buff[..i], iter_n.buff[..i]);

        // calc ==> {
        //   // if it's >= 0, max num of bits is 32
        //   iter_a.buff[i] as int - iter_n.buff[i] + A.full >= 0;
        //   // == x13

        //   carry_add - carry_sub + A.uh == 0;
        //   
        //   //int64_rs(to_int64(iter_a.buff[i] as int - iter_n.buff[i] + A.full), 32) >= 0;
        //   //A'.full == int64_rs(sub_mod32_update_A(A.full, iter_a.buff[i], iter_n.buff[i]), 32);
        //   //A'.lh == uint32_sub(uint32_add(carry_add, A.uh), carry_sub);
        //   //A'.lh == 0;

        //   A'.lh == 0 && A'.uh == 0;
        //   { lemma_int64_half_split(A'.full); }
        //   A'.full == 0;
        // }

        
        // A + a[i] - n[i]
        assume(iter_a.buff[i] as int - iter_n.buff[i] + A.full >= 0 ==> A'.full == 0);

        //assume(iter_a.buff[i] as int - iter_n.buff[i] - neg1_to_uint1(A.full) >= 0 ==> A'.full == 0);
        assume(iter_a.buff[i] as int - iter_n.buff[i] - neg1_to_uint1(A.full) < 0 ==> A'.full == -1);

        var (z, bout) := uint32_subb(iter_a_next.buff[i], iter_n_next.buff[i], neg1_to_uint1(A.full));
        assert(z == x13) by { reveal_uint32_sub(); }

        calc {
          zs_next;
          { assert(iter_a_next.buff[..i+1][..i] == iter_a.buff[..i]);
            assert(iter_n_next.buff[..i+1][..i] == iter_n.buff[..i]);
          }
          zs + [x13];
          iter_a'.buff[..i] + [x13];
          iter_a'_next.buff[..i+1];
        }

        calc {
          bin_next;
          { assert(iter_a_next.buff[..i+1][..i] == iter_a.buff[..i]);
            assert(iter_n_next.buff[..i+1][..i] == iter_n.buff[..i]);
          }
          neg1_to_uint1(A'.full);
        }
        
      }

}
