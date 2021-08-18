include "../spec/rsa_ops.dfy"
include "montmul_lemmas.dfy"
include "subb_lemmas.dfy"
include "../libraries/src/NonlinearArithmetic/DivMod.dfy"
include "../libraries/src/NonlinearArithmetic/Mul.dfy"
include "../libraries/src/NonlinearArithmetic/Power.dfy"

module modexp_var_lemmas {
    import opened bv_ops
    import opened vt_ops
    import opened rsa_ops
    import opened vt_consts
    import opened mont_loop_lemmas
    import opened montmul_lemmas
    import opened subb_lemmas
    import opened BASE_256_Seq
    import opened DivMod
    import opened Mul
    import opened Power

    predicate modexp_var_inv(
        a: nat,
        sig: nat,
        i: nat,
        rsa: rsa_params)
        requires rsa.M != 0;
    {
        LemmaPowPositiveAuto();
        IsModEquivalent(a, Pow(sig, Pow(2, i)) * rsa.R, rsa.M)
    }

    lemma modexp_var_inv_pre_lemma(
        a_view: seq<uint256>,
        rr: seq<uint256>,
        sig: seq<uint256>,
        rsa: rsa_params)

    requires montmul_inv(a_view, rr, NUM_WORDS, sig, rsa);
    requires ToNat(rr) == rsa.RR;
    ensures modexp_var_inv(ToNat(a_view), ToNat(sig), 0, rsa);
    {
        var m := rsa.M;
        var a := ToNat(a_view);
        var s := ToNat(sig);

        calc ==> {
            true;
                {
                    LemmaMulModNoopLeft(rsa.RR, rsa.R_INV, m);
                    LemmaMulModNoopLeft(rsa.R * rsa.R, rsa.R_INV, m);
                }
            IsModEquivalent(rsa.RR * rsa.R_INV, rsa.R * rsa.R * rsa.R_INV, m);
                {
                    LemmaMulProperties();
                    r_r_inv_cancel_lemma(rsa.RR * rsa.R_INV, rsa.R, rsa);
                }
            IsModEquivalent(rsa.RR * rsa.R_INV, rsa.R, m);
        }

        assert IsModEquivalent(a, s * rsa.R, m) by {
            assert IsModEquivalent(rsa.RR * rsa.R_INV * s, rsa.R * s, m) by {
                LemmaMulModNoopLeft(rsa.RR * rsa.R_INV, s, m);
                LemmaMulModNoopLeft(rsa.R, s, m);
            }
            assert IsModEquivalent(a, rsa.RR * rsa.R_INV * s, m) by {
                montmul_inv_lemma_1(a_view, rr, sig, rsa);
                LemmaMulProperties();
            }
        }
        
        reveal Pow();
    }

    lemma modexp_var_inv_peri_lemma(
        a_view: seq<uint256>,
        next_a_view: seq<uint256>,
        sig: nat,
        i: nat,
        rsa: rsa_params)

        requires montmul_inv(next_a_view, a_view, NUM_WORDS, a_view, rsa);
        requires modexp_var_inv(ToNat(a_view), sig, i, rsa);
        ensures modexp_var_inv(ToNat(next_a_view), sig, i + 1, rsa);
    {
        var m := rsa.M;
        var a := ToNat(a_view);
        var next_a := ToNat(next_a_view);

        LemmaPowPositiveAuto();
        LemmaPowNonnegativeAuto();
        LemmaMulNonnegativeAuto();
        var next_goal := Pow(sig, Pow(2, i + 1)) * rsa.R;

        assert IsModEquivalent(a, Pow(sig, Pow(2, i)) * rsa.R, m);
        
        calc ==> {
            IsModEquivalent(a, Pow(sig, Pow(2, i)) * rsa.R, m);
                {
                    LemmaMulModNoop(a, a, m);
                    LemmaMulModNoop(Pow(sig, Pow(2, i)) * rsa.R, Pow(sig, Pow(2, i)) * rsa.R, m);
                    LemmaMulProperties();
                }
            IsModEquivalent(a * a, Pow(sig, Pow(2, i)) * rsa.R * Pow(sig, Pow(2, i)) * rsa.R, m);
                { LemmaMulIsAssociativeAuto(); }
            IsModEquivalent(a * a, Pow(sig, Pow(2, i)) * Pow(sig, Pow(2, i)) * rsa.R * rsa.R, m);
                { LemmaPowAddsAuto(); }
            IsModEquivalent(a * a, Pow(sig, Pow(2, i) + Pow(2, i)) * rsa.R * rsa.R, m);
                { reveal Pow(); }
            IsModEquivalent(a * a, next_goal * rsa.R, m);
                {
                    LemmaMulModNoopLeft(a * a, rsa.R_INV, m);
                    LemmaMulModNoopLeft(next_goal * rsa.R, rsa.R_INV, m);
                }
            IsModEquivalent(a * a * rsa.R_INV, next_goal * rsa.R * rsa.R_INV, m);
                {
                    assert IsModEquivalent(next_a, a * a * rsa.R_INV, m) by {
                        montmul_inv_lemma_1(next_a_view, a_view, a_view, rsa);
                    }
                    LemmaMulIsAssociativeAuto();
                }
            IsModEquivalent(next_a, next_goal * rsa.R_INV * rsa.R, m);
                { r_r_inv_cancel_lemma(next_a, next_goal, rsa); }
            IsModEquivalent(next_a, next_goal, m);
        }

    }

    lemma modexp_var_inv_post_lemma(
        a_view: seq<uint256>,
        next_a_view: seq<uint256>,
        sig: seq<uint256>,
        rsa: rsa_params)

        requires montmul_inv(next_a_view, a_view, NUM_WORDS, sig, rsa);
        requires modexp_var_inv(ToNat(a_view), ToNat(sig), rsa.E0, rsa);
        ensures IsModEquivalent(ToNat(next_a_view), Pow(ToNat(sig), rsa.E), rsa.M);
    {
        var m := rsa.M;
        var a := ToNat(a_view);
        var next_a := ToNat(next_a_view);
        var s := ToNat(sig);

        LemmaPowPositiveAuto();
        LemmaPowNonnegativeAuto();
        var cur := Pow(s, Pow(2, rsa.E0));

        assert IsModEquivalent(a, cur * rsa.R, m);

        calc ==> {
            IsModEquivalent(a, cur * rsa.R, m);
                {
                    LemmaMulModNoopLeft(a, s * rsa.R_INV, m);
                    LemmaMulModNoopLeft(cur * rsa.R, s * rsa.R_INV, m);
                }
            IsModEquivalent(a * (s * rsa.R_INV), (cur * rsa.R) * (s * rsa.R_INV), m);
                { LemmaMulIsAssociativeAuto(); }
            IsModEquivalent(a * s * rsa.R_INV, cur * rsa.R * s * rsa.R_INV, m);
                {
                    assert IsModEquivalent(next_a, a * s * rsa.R_INV, m) by {
                        montmul_inv_lemma_1(next_a_view, a_view, sig, rsa);
                    }
                }
            IsModEquivalent(next_a, cur * rsa.R * s * rsa.R_INV, m);
                {
                    LemmaMulProperties();
                    r_r_inv_cancel_lemma(next_a, cur * s, rsa);
                }
            IsModEquivalent(next_a, cur * s, m);
                {
                    LemmaMulIsCommutativeAuto();
                    reveal Pow();
                }
            IsModEquivalent(next_a, Pow(s, Pow(2, rsa.E0) + 1), m);
            IsModEquivalent(next_a, Pow(s, rsa.E), m);
            IsModEquivalent(ToNat(next_a_view), Pow(ToNat(sig), rsa.E), m);
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
        rsa: rsa_params)

    requires rsa_params_inv(rsa);
    requires raw_val < rsa.SIG + rsa.M;
    requires IsModEquivalent(raw_val, Pow(rsa.SIG, rsa.E), rsa.M);
    requires carry ==> raw_val < rsa.M;
    requires !carry ==> raw_val - rsa.M == adjusted_val;

    ensures carry ==> raw_val == Pow(rsa.SIG, rsa.E) % rsa.M;
    ensures !carry ==> adjusted_val == Pow(rsa.SIG, rsa.E) % rsa.M;
    {
        if carry {
            LemmaModLessThanDivisor(raw_val, rsa.M);
            assert raw_val == Pow(rsa.SIG, rsa.E) % rsa.M;
        } else {
            calc ==> {
                true;
                    { LemmaSubModNoopRight(raw_val, rsa.M as int, rsa.M); }
                IsModEquivalent(raw_val, adjusted_val, rsa.M);
                IsModEquivalent(adjusted_val, Pow(rsa.SIG, rsa.E), rsa.M);
            }

            LemmaModLessThanDivisor(adjusted_val, rsa.M);
        }
    }
}