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
        key: pub_key)
        requires key.m != 0;
    {
        cong(a, power(sig, power(2, i)) * key.R, key.m)
    }

    lemma modexp_var_inv_lemma_0(
        a_slice: seq<uint256>,
        rr: seq<uint256>,
        sig: seq<uint256>,
        key: pub_key)

    requires montmul_inv(a_slice, rr, NUM_WORDS, sig, key);
    requires to_nat(rr) == key.RR;
    ensures modexp_var_inv(to_nat(a_slice), to_nat(sig), 0, key);
    {
        var m := key.m;
        var a := to_nat(a_slice);
        var s := to_nat(sig);

        assert cong(key.RR * key.R_INV, key.R, m) by {
            assert cong(key.R * key.R * key.R_INV, key.R, m) by {
                r_r_inv_cancel_lemma(key.R, key);
            }
            assert cong(key.RR * key.R_INV, key.R * key.R * key.R_INV, m) by {
                assert cong(key.RR, key.R * key.R, m);
                cong_mul_lemma_1(key.RR, key.R * key.R, key.R_INV, m);
            }
            reveal cong();
        }

        assert cong(a, s * key.R, m) by {
            assert cong(key.RR * key.R_INV * s, key.R * s, m) by {
                cong_mul_lemma_1(key.RR * key.R_INV, key.R, s, m);
            }
            assert cong(a, key.RR * key.R_INV * s, m) by {
                montmul_inv_lemma_1(a_slice, rr, sig, key);
            }
            reveal cong();
        }
        
        reveal power();
    }

    lemma modexp_var_inv_lemma_1(
        a_slice: seq<uint256>,
        next_a_slice: seq<uint256>,
        sig: nat,
        i: nat,
        key: pub_key)

        requires montmul_inv(next_a_slice, a_slice, NUM_WORDS, a_slice, key);
        requires modexp_var_inv(to_nat(a_slice), sig, i, key);
        ensures modexp_var_inv(to_nat(next_a_slice), sig, i + 1, key);
    {
        var m := key.m;
        var a := to_nat(a_slice);
        var next_a := to_nat(next_a_slice);
        var next_goal := power(sig, power(2, i + 1)) * key.R;

        assert cong(a, power(sig, power(2, i)) * key.R, m);
        
        calc ==> {
            cong(a, power(sig, power(2, i)) * key.R, m);
                { cong_mul_lemma_2(a, power(sig, power(2, i)) * key.R, 
                    a, power(sig, power(2, i)) * key.R, m); }
            cong(a * a, power(sig, power(2, i)) * key.R * power(sig, power(2, i)) * key.R, m);
                { power_same_base_lemma(sig, power(2, i), power(2, i)); }
            cong(a * a, power(sig, power(2, i) + power(2, i)) * key.R * key.R, m);
            cong(a * a, power(sig, power(2, i) * 2) * key.R * key.R, m);
                { power_add_one_lemma(2, i); }
            cong(a * a, next_goal * key.R, m);
                { cong_mul_lemma_1(a * a, next_goal * key.R, key.R_INV, m); }
            cong(a * a * key.R_INV, next_goal * key.R * key.R_INV, m);
                {
                    assert cong(next_a, a * a * key.R_INV, m) by {
                        montmul_inv_lemma_1(next_a_slice, a_slice, a_slice, key);
                    }
                    cong_trans_lemma(next_a, a * a * key.R_INV, next_goal * key.R * key.R_INV, m);
                }
            cong(next_a, next_goal * key.R_INV * key.R, m);
                { r_r_inv_cancel_lemma_2(next_a, next_goal, key); }
            cong(next_a, next_goal, m);
        }

    }

    lemma modexp_var_inv_lemma_2(
        a_slice: seq<uint256>,
        next_a_slice: seq<uint256>,
        sig: seq<uint256>,
        key: pub_key)

        requires montmul_inv(next_a_slice, a_slice, NUM_WORDS, sig, key);
        requires modexp_var_inv(to_nat(a_slice), to_nat(sig), key.e', key);
        ensures cong(to_nat(next_a_slice), power(to_nat(sig), key.e), key.m);
    {
        var m := key.m;
        var a := to_nat(a_slice);
        var next_a := to_nat(next_a_slice);
        var s := to_nat(sig);
        var cur := power(s, power(2, key.e'));

        assert cong(a, cur * key.R, m);

        calc ==> {
            cong(a, cur * key.R, m);
                { cong_mul_lemma_1(a, cur * key.R, s * key.R_INV, m); }
            cong(a * (s * key.R_INV), (cur * key.R) * (s * key.R_INV), m);
                {
                    assert a * (s * key.R_INV) == a * s * key.R_INV;
                    assert (cur * key.R) * (s * key.R_INV) == cur * key.R * s * key.R_INV;
                }
            cong(a * s * key.R_INV, cur * key.R * s * key.R_INV, m);
                {
                    assert cong(next_a, a * s * key.R_INV, m) by {
                        montmul_inv_lemma_1(next_a_slice, a_slice, sig, key);
                    }
                    cong_trans_lemma(next_a, a * s * key.R_INV, cur * key.R * s * key.R_INV, m);
                }
            cong(next_a, cur * key.R * s * key.R_INV, m);
                { r_r_inv_cancel_lemma_2(next_a, cur * s, key); }
            cong(next_a, cur * s, m);
                { power_add_one_lemma(s, power(2, key.e')); }
            cong(next_a, power(s, power(2, key.e') + 1), m);
            cong(next_a, power(s, key.e), m);
            cong(to_nat(next_a_slice), power(to_nat(sig), key.e), m);
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
        key: pub_key)

    requires pub_key_inv(key);
    requires raw_val < sig + key.m;
    requires cong(raw_val, power(sig, key.e), key.m);
    requires carry ==> raw_val < key.m;
    requires !carry ==> raw_val - key.m == adjusted_val;

    ensures carry ==> raw_val == power(sig, key.e) % key.m;
    ensures !carry ==> adjusted_val == power(sig, key.e) % key.m;
    {
        if carry {
            cong_remainder_lemma(raw_val, power(sig, key.e), key.m);
            assert raw_val == power(sig, key.e) % key.m;
        } else {
            assume sig < key.m; // TODO: fix this
            calc ==> {
                true;
                    { cong_add_lemma_3(raw_val, -(key.m as int), key.m); }
                cong(raw_val, adjusted_val, key.m);
                    {
                        cong_trans_lemma(adjusted_val, raw_val, power(sig, key.e), key.m);
                    }
                cong(adjusted_val, power(sig, key.e), key.m);
            }

            cong_remainder_lemma(adjusted_val, power(sig, key.e), key.m);
        }
    }
}