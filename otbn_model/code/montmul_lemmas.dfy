include "mont_loop_lemmas.dfy"

module montmul_lemmas {
    import opened bv_ops
    import opened vt_ops
    import opened rsa_ops
    import opened vt_consts
    import opened powers
    import opened congruences
    import opened mont_loop_lemmas

    lemma montmul_inv_lemma_0(
        a: seq<uint256>,
        x: seq<uint256>, 
        i: nat,
        y: seq<uint256>, 
        key: pub_key)

        requires |a| == |x| == |y| == NUM_WORDS;
        requires to_nat(a) == 0;
        requires pub_key_inv(key);
        requires i == 0;
        
        ensures montmul_inv(a, x, i, y, key);
    {
        assert to_nat(x[..i]) == 0 by {
            reveal to_nat();
        }
        reveal cong();
        assert montmul_inv(a, x, i, y, key);
    }

    lemma r_r_inv_cancel_lemma(a: nat, key: pub_key)
        requires pub_key_inv(key);
        ensures cong(a * key.R_INV * key.R, a, key.m);
    {
        assert cong(key.R_INV * key.R, 1, key.m);
        cong_mul_lemma_1(key.R_INV * key.R, 1, a, key.m);
    }
    
    lemma r_r_inv_cancel_lemma_2(a: nat, b : nat, key: pub_key)
        requires pub_key_inv(key);
        requires cong(a, b * key.R_INV * key.R, key.m);
        ensures cong(a, b, key.m);
    {
        assert cong(b * key.R_INV * key.R, b, key.m) by {
            r_r_inv_cancel_lemma(b, key);
        }
        reveal cong();
    }

    lemma montmul_inv_lemma_1(a_slice: seq<uint256>,
        x: seq<uint256>,
        y: seq<uint256>,
        key: pub_key)
    
        requires montmul_inv(a_slice, x, NUM_WORDS, y, key);
        ensures cong(to_nat(a_slice), to_nat(x) * to_nat(y) * key.R_INV, key.m);
    {
        var m := key.m;
        var a := to_nat(a_slice);
        assert x[..NUM_WORDS] == x;

        calc ==> {
            cong(a * key.R, to_nat(x) * to_nat(y), m);
                { cong_mul_lemma_1(a * key.R, to_nat(x) * to_nat(y), key.R_INV, m); }
            cong(a * key.R * key.R_INV, to_nat(x) * to_nat(y) * key.R_INV, m);
                { reveal cong(); }
            cong(to_nat(x) * to_nat(y) * key.R_INV, a * key.R * key.R_INV, m);
                { r_r_inv_cancel_lemma_2(to_nat(x) * to_nat(y) * key.R_INV, a, key); }
            cong(to_nat(x) * to_nat(y) * key.R_INV, a, m);
                { reveal cong(); }
            cong(a, to_nat(x) * to_nat(y) * key.R_INV, m);
        }
    }
}