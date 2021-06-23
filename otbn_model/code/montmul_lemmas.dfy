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
        rsa: rsa_params)

        requires |a| == |x| == |y| == NUM_WORDS;
        requires to_nat(a) == 0;
        requires rsa_params_inv(rsa);
        requires i == 0;
        
        ensures montmul_inv(a, x, i, y, rsa);
    {
        assert to_nat(x[..i]) == 0 by {
            reveal to_nat();
        }
        reveal cong();
        assert montmul_inv(a, x, i, y, rsa);
    }

    lemma r_r_inv_cancel_lemma(a: nat, b : nat, rsa: rsa_params)
        requires rsa_params_inv(rsa);
        requires cong(a, b * rsa.R_INV * rsa.R, rsa.M);
        ensures cong(a, b, rsa.M);
    {
        assert cong(b * rsa.R_INV * rsa.R, b, rsa.M) by {
            assert cong(rsa.R_INV * rsa.R, 1, rsa.M);
            cong_mul_lemma_1(rsa.R_INV * rsa.R, 1, b, rsa.M);
        }
        reveal cong();
    }

    lemma montmul_inv_lemma_1(
        a_view: seq<uint256>,
        x: seq<uint256>,
        y: seq<uint256>,
        rsa: rsa_params)
    
        requires montmul_inv(a_view, x, NUM_WORDS, y, rsa);
        ensures cong(to_nat(a_view), to_nat(x) * to_nat(y) * rsa.R_INV, rsa.M);
    {
        var m := rsa.M;
        var a := to_nat(a_view);
        assert x[..NUM_WORDS] == x;

        calc ==> {
            cong(a * rsa.R, to_nat(x) * to_nat(y), m);
                { cong_mul_lemma_1(a * rsa.R, to_nat(x) * to_nat(y), rsa.R_INV, m); }
            cong(a * rsa.R * rsa.R_INV, to_nat(x) * to_nat(y) * rsa.R_INV, m);
                { reveal cong(); }
            cong(to_nat(x) * to_nat(y) * rsa.R_INV, a * rsa.R * rsa.R_INV, m);
                { r_r_inv_cancel_lemma(to_nat(x) * to_nat(y) * rsa.R_INV, a, rsa); }
            cong(to_nat(x) * to_nat(y) * rsa.R_INV, a, m);
                { reveal cong(); }
            cong(a, to_nat(x) * to_nat(y) * rsa.R_INV, m);
        }
    }
}