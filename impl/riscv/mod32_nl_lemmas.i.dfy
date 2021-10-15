include "rsa_ops.i.dfy"
include "../../lib/bv_ops_nl.dfy"

module mod32_nl_lemmas {
    import opened bv_ops
    import opened bv_ops_nl
    import opened rsa_ops
    import opened rv_machine
    import opened BASE_32_Seq
    import Power2

    lemma uinteresting(lh: uint32, uh: uint32)
        requires lh == 0xffff_ffff || lh == 0
        requires uh == to_uint32(int32_rs(to_int32(lh), 31))
        ensures lh == 0 ==> uh == 0
        ensures lh == 0xffff_ffff ==> uh == 0xffff_ffff
        ensures uh == 0 || uh == 0xffff_ffff
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

    lemma uninteresting2(num: int64_view_t)
        ensures num.full == -1 ==> num.lh == 0xffff_ffff;
        ensures num.full == 0 ==> num.lh == 0;
    {
        lemma_int64_half_split(num);
        assert num.lh + num.uh * BASE_32 == to_2s_complement_bv64(num.full);

        if num.full == 0 {
            assert num.lh == 0;
        }
        
        if num.full == -1 {
            assert to_2s_complement_bv64(num.full) == BASE_64 - 1;
            if num.lh != 0xffff_ffff {
                assert false;
            }
        }
    }

    lemma sub_mod32_A_bound_lemma(A: int, a: uint32, n: uint32)
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

    function sub_mod32_update_A(A: int64, a: uint32, n: uint32) : int64
    requires A == 0 || A == -1
    {
        sub_mod32_A_bound_lemma(A, a, n);
        int64_rs(A + a - n, 32)
    }

    lemma sub_mod32_update_A_lemma(A: int, A': int, a_i: uint32, n_i: uint32, bin_next: uint1)
        requires A == 0 || A == -1
        requires A' == 0 || A' == -1
        requires bin_next == if a_i >= n_i + neg1_to_uint1(A) then 0 else 1
        requires A' == sub_mod32_update_A(A, a_i, n_i)
        ensures bin_next == neg1_to_uint1(A')
    {
    }
}
