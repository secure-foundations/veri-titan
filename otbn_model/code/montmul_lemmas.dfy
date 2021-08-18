include "mont_loop_lemmas.dfy"
include "../libraries/src/NonlinearArithmetic/DivMod.dfy"
include "../libraries/src/NonlinearArithmetic/Mul.dfy"

module montmul_lemmas {
    import opened bv_ops
    import opened vt_ops
    import opened rsa_ops
    import opened vt_consts
    import opened mont_loop_lemmas
    import opened BASE_256_Seq
    import opened DivMod
    import opened Mul

    lemma montmul_inv_lemma_0(
        a: seq<uint256>,
        x: seq<uint256>, 
        i: nat,
        y: seq<uint256>, 
        rsa: rsa_params)

        requires |a| == |x| == |y| == NUM_WORDS;
        requires ToNat(a) == 0;
        requires rsa_params_inv(rsa);
        requires i == 0;
        
        ensures montmul_inv(a, x, i, y, rsa);
    {
        assert ToNat(x[..i]) == 0 by {
            reveal ToNat();
        }
        assert montmul_inv(a, x, i, y, rsa);
    }

    lemma r_r_inv_cancel_lemma(a: nat, b: nat, rsa: rsa_params)
        requires rsa_params_inv(rsa);
        requires IsModEquivalent(a, b * rsa.R_INV * rsa.R, rsa.M);
        ensures IsModEquivalent(a, b, rsa.M);
    {
        assert IsModEquivalent(b * rsa.R_INV * rsa.R, b, rsa.M) by {
            assert IsModEquivalent(rsa.R_INV * rsa.R, 1, rsa.M);
            LemmaMulModNoopLeft(rsa.R_INV * rsa.R, b, rsa.M);
            LemmaMulModNoopLeft(1, b, rsa.M);
            LemmaMulIsAssociativeAuto();
        }
    }

    lemma montmul_inv_lemma_1(
        a_view: seq<uint256>,
        x: seq<uint256>,
        y: seq<uint256>,
        rsa: rsa_params)
    
        requires montmul_inv(a_view, x, NUM_WORDS, y, rsa);
        ensures IsModEquivalent(ToNat(a_view), ToNat(x) * ToNat(y) * rsa.R_INV, rsa.M);
    {
        var m := rsa.M;
        var a := ToNat(a_view);
        assert x[..NUM_WORDS] == x;

        calc ==> {
            IsModEquivalent(a * rsa.R, ToNat(x) * ToNat(y), m);
                {
                    LemmaMulModNoopLeft(a * rsa.R, rsa.R_INV, m);
                    LemmaMulModNoopLeft(ToNat(x) * ToNat(y), rsa.R_INV, m);
                }
            IsModEquivalent(a * rsa.R * rsa.R_INV, ToNat(x) * ToNat(y) * rsa.R_INV, m);
            IsModEquivalent(ToNat(x) * ToNat(y) * rsa.R_INV, a * rsa.R * rsa.R_INV, m);
                {
                    LemmaMulIsAssociativeAuto();
                    LemmaMulNonnegativeAuto();
                    r_r_inv_cancel_lemma(ToNat(x) * ToNat(y) * rsa.R_INV, a, rsa);
                }
            IsModEquivalent(ToNat(x) * ToNat(y) * rsa.R_INV, a, m);
            IsModEquivalent(a, ToNat(x) * ToNat(y) * rsa.R_INV, m);
        }
    }
}