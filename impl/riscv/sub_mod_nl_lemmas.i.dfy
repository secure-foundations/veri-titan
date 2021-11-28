include "rsa_ops.i.dfy"
include "../../lib/bv_ops_nl.dfy"

module sub_mod_nl_lemmas {
    import opened bv_ops
    import opened bv_ops_nl
    import opened rv_machine
    import opened BASE_32_Seq
    import Power2

    lemma refine_int64_view(lh: uint32, uh: uint32, full: int64) returns (r: int64_view_t)
      requires lh == uint64_lh(to_2s_complement_bv64(full));
      requires uh == uint64_uh(to_2s_complement_bv64(full));
      ensures valid_int64_view(r, lh, uh)
    {
      r := int64_cons(lh, uh, full);
      lemma_int64_half_split(r);
      assert valid_int64_view(r, lh, uh);
    }

    lemma A_zero() returns (r: int64_view_t)
    ensures r == int64_cons(0, 0, 0);
    {
        reveal uint64_lh();
        reveal uint64_uh();
        r := refine_int64_view(0, 0, 0);
    }

    lemma A_neg_one() returns (r: int64_view_t)
    ensures r == int64_cons(0xffff_ffff, 0xffff_ffff, -1);
    {
        reveal uint64_lh();
        reveal uint64_uh();
        r := refine_int64_view(0xffff_ffff, 0xffff_ffff, -1);
    }

    predicate sub_mod_A_inv(A: int64_raw)
    {
        && A.lh == uint64_lh(to_2s_complement_bv64(A.full))
        && A.uh == uint64_uh(to_2s_complement_bv64(A.full))
        && ((A.full == A.lh == A.uh == 0) || (A.full == -1 && (A.lh == A.uh == 0xffff_ffff)))
    }

    function A_as_carry(A: int) : uint1
      requires -1 <= A <= 0;
    {
      if A == -1 then 1 else 0
    }

    lemma A_halves_equal(lh: uint32, uh: uint32)
        requires lh == 0xffff_ffff || lh == 0
        requires uh == to_uint32(int32_rs(to_int32(lh), 31))
        ensures lh == uh
    {
        if lh == 0 {
            assert uh == to_uint32(int32_rs(0, 31));
            assert int32_rs(0, 31) == 0;
            assert uh == 0;
        } else {
            calc == {
                uh;
                to_uint32(int32_rs(to_int32(lh), 31));
                to_uint32(int32_rs(-1, 31));
                to_uint32(-1 / Power2.Pow2(31));
                {
                    Power2.Lemma2To64();
                    div_negative_one(Power2.Pow2(31));
                }
                to_uint32(-1);
                0xffff_ffff;
            }
        }
    }

    lemma A_value_special(A: int64_view_t)
        requires A.lh == A.uh 
        ensures (A.lh == 0xffff_ffff) <==> A.full == -1
        ensures (A.lh == 0) <==> A.full == 0
    {
        lemma_int64_half_split(A);
        if A.full == -1 {
            assert to_2s_complement_bv64(A.full) == BASE_64 - 1;
            if A.lh != 0xffff_ffff {
                assert false;
            }
        }
    }

    lemma sub_mod_A_bound_lemma(A: int, a: uint32, n: uint32)
    requires A == 0 || A == -1
    ensures -BASE_63 <= (A + a - n) <= BASE_63 - 1
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

    function sub_mod_update_A(A: int64, a: uint32, n: uint32) : int64
    requires A == 0 || A == -1
    {
        sub_mod_A_bound_lemma(A, a, n);
        int64_rs(A + a - n, 32)
    }

    lemma sub_mod_update_A_lemma(A: int, A': int, a_i: uint32, n_i: uint32, bin_next: uint1)
        requires A == 0 || A == -1
        requires A' == 0 || A' == -1
        requires bin_next == if a_i >= n_i + A_as_carry(A) then 0 else 1
        requires A' == sub_mod_update_A(A, a_i, n_i)
        ensures bin_next == A_as_carry(A')
    {
    }

    lemma int64_rs_properties(pre_shift: int, a: uint32, n: uint32)
        requires pre_shift == a - n - 1 || pre_shift == a - n;
        ensures pre_shift >= 0 ==> int64_rs(pre_shift, 32) == 0;
        ensures pre_shift < 0 ==> int64_rs(pre_shift, 32) == -1;
    {
        Power2.Lemma2To64();
        if pre_shift >= 0 {
            assert 0 <= pre_shift <= BASE_32 - 1;
            assert int64_rs(pre_shift, 32) == 0;
        } else {
            assert int64_rs(pre_shift, 32) == -1;
        }
    }

    lemma update_A_correct(
        A: int64_view_t,
        a_i: uint32, n_i: uint32,
        v0: uint32, v1: uint32,
        lh: uint32, uh: uint32,
        carry_add: uint32,
        carry_sub: uint32)
    returns (A': int64_view_t)

        requires sub_mod_A_inv(A)
        requires v0 == uint32_add(A.lh, a_i);
        requires carry_add == uint32_lt(v0, a_i);
        requires carry_sub == uint32_lt(v0, uint32_sub(v0, n_i));
        requires v1 == uint32_add(A.uh, carry_add);
        requires lh == uint32_sub(v1, carry_sub);
        requires uh == to_uint32(int32_rs(to_int32(lh), 31));

        ensures sub_mod_A_inv(A')
        ensures A' == int64_cons(lh, uh, A'.full)
        ensures A'.full == sub_mod_update_A(A.full, a_i, n_i);
    {
        A_halves_equal(lh, uh);
        // A_value_special(A');
        A_value_special(A);

        if A.lh == 0xffff_ffff {
            ghost var pre_shift := a_i - n_i - 1;

            if carry_add == 1 {
                assert v0 == a_i - 1;
                assert v1 == uint32_add(0xffff_ffff, 1) == 0;
                if pre_shift >= 0 {
                    // assert carry_sub == 0;
                    assert lh == uh == 0;
                    // assert A'.full == 0;
                    int64_rs_properties(pre_shift, a_i, n_i);
                    A' := A_zero();
                } else {
                    // assert carry_sub == 1;
                    assert lh == uh == 0xffff_ffff;
                    // assert A'.full == -1;
                    int64_rs_properties(pre_shift, a_i, n_i);
                    A' := A_neg_one();
                }
            } else {
                assert pre_shift < 0;
                assert v0 == 0xffff_ffff + a_i;
                assert v1 == uint32_add(0xffff_ffff, 0) == 0xffff_ffff;
                assert carry_sub == 0;
                assert lh == uh == 0xffff_ffff;
                // assert A'.full == -1;
                int64_rs_properties(pre_shift, a_i, n_i);
                A' := A_neg_one();
            }
            // assert A'.full == int64_rs(A.full + a_i - n_i, 32);
        } else {
            ghost var pre_shift := a_i - n_i;
        
            if pre_shift < 0 {
                assert a_i - n_i < 0;
                assert carry_sub == 1;
                assert lh == uh == 0xffff_ffff;
                // assert A'.full == -1;
                int64_rs_properties(pre_shift, a_i, n_i);
                A' := A_neg_one();
            } else {
                assert carry_sub == 0;
                assert lh == uh == 0;
                // assert A'.full == 0;
                int64_rs_properties(pre_shift, a_i, n_i);
                A' := A_zero();
            }
        }
    }
}
