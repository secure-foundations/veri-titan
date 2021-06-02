include "../spec/rsa_ops.dfy"
include "montmul_lemmas.dfy"

module modexp_var_lemmas {
    import opened bv_ops
    import opened vt_ops
    import opened rsa_ops
    import opened vt_consts
    import opened powers
    import opened congruences
    import opened mont_loop_lemmas
    import opened montmul_lemmas

    predicate subb_inv(
        dst: seq<uint256>,
        carry: uint1,
        src1: seq<uint256>,
        src2: seq<uint256>,
        index: nat)

    requires |dst| == |src1| == |src2|;
    requires index <= |src1|;
    {
        (dst[..index], carry)
            == seq_subb(src1[..index], src2[..index])
    }

    lemma subb_inv_peri_lemma(
        dst: seq<uint256>,
        new_carry: uint1,
        src1: seq<uint256>,
        src2: seq<uint256>,
        old_carry: uint1,
        index: nat)
    requires |dst| == |src1| == |src2|;
    requires index < |src1|;
    requires subb_inv(dst, old_carry, src1, src2, index);
    requires (dst[index], new_carry)
        == uint256_subb(src1[index], src2[index], old_carry);
    ensures subb_inv(dst, new_carry, src1, src2, index + 1);
    {
        var (zs, bin) := seq_subb(src1[..index], src2[..index]);
        var (z, bout) := uint256_subb(src1[index], src2[index], old_carry);

        assert dst[..index+1] == zs + [z];
        assert src1[..index+1] == src1[..index] + [src1[index]];
        assert src2[..index+1] == src2[..index] + [src2[index]];
    }

    lemma subb_inv_post_lemma(
        dst: seq<uint256>,
        carry: uint1,
        src1: seq<uint256>,
        src2: seq<uint256>)
        
    requires |dst| == |src1| == |src2|;
    requires subb_inv(dst, carry, src1, src2, |dst|);
    ensures carry == 0 ==> to_nat(src1) - to_nat(src2) == to_nat(dst);
    ensures carry == 1 ==> to_nat(src1) < to_nat(src2);
    {
        var index := |dst|;
        assert dst[..index] == dst;
        assert src1[..index] == src1;
        assert src2[..index] == src2;
    
        seq_subb_nat_lemma(src1, src2, dst, carry);

        assert to_nat(src1) - to_nat(src2) + carry * pow_B256(index) == to_nat(dst);

        to_nat_bound_lemma(dst);
    }

    predicate modexp_var_inv(
        a: nat,
        sig: nat,
        i: nat,
        rsa: rsa_params)
        requires rsa.m != 0;
    {
        cong(a, power(sig, power(2, i)) * rsa.R, rsa.m)
    }

    lemma modexp_var_inv_lemma_0(
        a_view: seq<uint256>,
        rr: seq<uint256>,
        sig: seq<uint256>,
        rsa: rsa_params)

    requires montmul_inv(a_view, rr, NUM_WORDS, sig, rsa);
    requires to_nat(rr) == rsa.RR;
    ensures modexp_var_inv(to_nat(a_view), to_nat(sig), 0, rsa);
    {
        var m := rsa.m;
        var a := to_nat(a_view);
        var s := to_nat(sig);

        assert cong(rsa.RR * rsa.R_INV, rsa.R, m) by {
            assert cong(rsa.R * rsa.R * rsa.R_INV, rsa.R, m) by {
                r_r_inv_cancel_lemma(rsa.R, rsa);
            }
            assert cong(rsa.RR * rsa.R_INV, rsa.R * rsa.R * rsa.R_INV, m) by {
                assert cong(rsa.RR, rsa.R * rsa.R, m);
                cong_mul_lemma_1(rsa.RR, rsa.R * rsa.R, rsa.R_INV, m);
            }
            reveal cong();
        }

        assert cong(a, s * rsa.R, m) by {
            assert cong(rsa.RR * rsa.R_INV * s, rsa.R * s, m) by {
                cong_mul_lemma_1(rsa.RR * rsa.R_INV, rsa.R, s, m);
            }
            assert cong(a, rsa.RR * rsa.R_INV * s, m) by {
                montmul_inv_lemma_1(a_view, rr, sig, rsa);
            }
            reveal cong();
        }
        
        reveal power();
    }

    lemma modexp_var_inv_lemma_1(
        a_view: seq<uint256>,
        next_a_view: seq<uint256>,
        sig: nat,
        i: nat,
        rsa: rsa_params)

        requires montmul_inv(next_a_view, a_view, NUM_WORDS, a_view, rsa);
        requires modexp_var_inv(to_nat(a_view), sig, i, rsa);
        ensures modexp_var_inv(to_nat(next_a_view), sig, i + 1, rsa);
    {
        var m := rsa.m;
        var a := to_nat(a_view);
        var next_a := to_nat(next_a_view);
        var next_goal := power(sig, power(2, i + 1)) * rsa.R;

        assert cong(a, power(sig, power(2, i)) * rsa.R, m);
        
        calc ==> {
            cong(a, power(sig, power(2, i)) * rsa.R, m);
                { cong_mul_lemma_2(a, power(sig, power(2, i)) * rsa.R, 
                    a, power(sig, power(2, i)) * rsa.R, m); }
            cong(a * a, power(sig, power(2, i)) * rsa.R * power(sig, power(2, i)) * rsa.R, m);
                { power_same_base_lemma(sig, power(2, i), power(2, i)); }
            cong(a * a, power(sig, power(2, i) + power(2, i)) * rsa.R * rsa.R, m);
            cong(a * a, power(sig, power(2, i) * 2) * rsa.R * rsa.R, m);
                { power_add_one_lemma(2, i); }
            cong(a * a, next_goal * rsa.R, m);
                { cong_mul_lemma_1(a * a, next_goal * rsa.R, rsa.R_INV, m); }
            cong(a * a * rsa.R_INV, next_goal * rsa.R * rsa.R_INV, m);
                {
                    assert cong(next_a, a * a * rsa.R_INV, m) by {
                        montmul_inv_lemma_1(next_a_view, a_view, a_view, rsa);
                    }
                    cong_trans_lemma(next_a, a * a * rsa.R_INV, next_goal * rsa.R * rsa.R_INV, m);
                }
            cong(next_a, next_goal * rsa.R_INV * rsa.R, m);
                { r_r_inv_cancel_lemma_2(next_a, next_goal, rsa); }
            cong(next_a, next_goal, m);
        }

    }

    lemma modexp_var_inv_lemma_2(
        a_view: seq<uint256>,
        next_a_view: seq<uint256>,
        sig: seq<uint256>,
        rsa: rsa_params)

        requires montmul_inv(next_a_view, a_view, NUM_WORDS, sig, rsa);
        requires modexp_var_inv(to_nat(a_view), to_nat(sig), rsa.e', rsa);
        ensures cong(to_nat(next_a_view), power(to_nat(sig), rsa.e), rsa.m);
    {
        var m := rsa.m;
        var a := to_nat(a_view);
        var next_a := to_nat(next_a_view);
        var s := to_nat(sig);
        var cur := power(s, power(2, rsa.e'));

        assert cong(a, cur * rsa.R, m);

        calc ==> {
            cong(a, cur * rsa.R, m);
                { cong_mul_lemma_1(a, cur * rsa.R, s * rsa.R_INV, m); }
            cong(a * (s * rsa.R_INV), (cur * rsa.R) * (s * rsa.R_INV), m);
                {
                    assert a * (s * rsa.R_INV) == a * s * rsa.R_INV;
                    assert (cur * rsa.R) * (s * rsa.R_INV) == cur * rsa.R * s * rsa.R_INV;
                }
            cong(a * s * rsa.R_INV, cur * rsa.R * s * rsa.R_INV, m);
                {
                    assert cong(next_a, a * s * rsa.R_INV, m) by {
                        montmul_inv_lemma_1(next_a_view, a_view, sig, rsa);
                    }
                    cong_trans_lemma(next_a, a * s * rsa.R_INV, cur * rsa.R * s * rsa.R_INV, m);
                }
            cong(next_a, cur * rsa.R * s * rsa.R_INV, m);
                { r_r_inv_cancel_lemma_2(next_a, cur * s, rsa); }
            cong(next_a, cur * s, m);
                { power_add_one_lemma(s, power(2, rsa.e')); }
            cong(next_a, power(s, power(2, rsa.e') + 1), m);
            cong(next_a, power(s, rsa.e), m);
            cong(to_nat(next_a_view), power(to_nat(sig), rsa.e), m);
        }

    }

    function mod(a: int, n: nat): int
        requires n != 0;
    {
        a % n
    }

    lemma modexp_var_correct_lemma(
        raw_val: nat,
        adjusted_val: nat,
        carry: bool,
        sig: nat,
        rsa: rsa_params)

    requires rsa_params_inv(rsa);
    requires raw_val < sig + rsa.m;
    requires cong(raw_val, power(sig, rsa.e), rsa.m);
    requires carry ==> raw_val < rsa.m;
    requires !carry ==> raw_val - rsa.m == adjusted_val;

    ensures carry ==> raw_val == power(sig, rsa.e) % rsa.m;
    ensures !carry ==> adjusted_val == power(sig, rsa.e) % rsa.m;
    {
        if carry {
            cong_remainder_lemma(raw_val, power(sig, rsa.e), rsa.m);
            assert raw_val == power(sig, rsa.e) % rsa.m;
        } else {
            assume sig < rsa.m; // TODO: fix this
            calc ==> {
                true;
                    { cong_add_lemma_3(raw_val, -(rsa.m as int), rsa.m); }
                cong(raw_val, adjusted_val, rsa.m);
                    {
                        cong_trans_lemma(adjusted_val, raw_val, power(sig, rsa.e), rsa.m);
                    }
                cong(adjusted_val, power(sig, rsa.e), rsa.m);
            }

            cong_remainder_lemma(adjusted_val, power(sig, rsa.e), rsa.m);
        }
    }
}