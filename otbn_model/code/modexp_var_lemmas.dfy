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
}