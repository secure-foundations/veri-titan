include "pow2.dfy"
import opened Power
import opened DivMod
import opened pows_of_2

module omegas {
    import opened Power
    import opened DivMod
    import opened Mul
    import opened pows_of_2

    const G: nat := 7 // 2048-th root of unity
    // const GI: nat := 8778

    const Q: nat := 12289
    const L: nat := 11
    const N: nat := 2048

    type elem = i :nat | i < Q

    lemma {:axiom} nth_root_lemma()
        ensures Pow2(L) == N;
        // 2 ** 11 == 2048
        ensures Pow(G, Pow2(L)) % Q == 1;
        // pow(7, 2 ** 11, 12289) == 1
        ensures Pow(G, Pow2(L)/2) % Q == Q - 1;
        // pow(7, 2 ** 10, 12289) == 12288

    lemma {:axiom} ntt_cancellation_lemma(n: pow2_t, k: nat)
        requires n.exp != 0;
        requires n.exp <= L
        ensures omega_nk(pow2_half(n), k) == omega_nk(n, 2 * k);

   function method modpow(a: elem, b: nat): elem
    {
        Pow(a, b) % Q
    }

    function method modmul(a: elem, b: elem): elem
    {
        (a * b) % Q
    }

    function method modadd(a: elem, b: elem): elem
    {
        (a + b) % Q
    }

    function method modsub(a: elem, b: elem): elem
    {
        (a - b) % Q
    }

    function method omega_n(n: pow2_t): elem
        requires n.exp <= L
    {
        Pow(G, Pow2(L - n.exp)) % Q
    }

    function method omega_nk(n: pow2_t, k: nat): elem
        requires n.exp <= L
    {
        Pow(omega_n(n), k) % Q
    }

    lemma omega_nk_mul_lemma(n: pow2_t, k1: nat, k2: nat)
        requires n.exp <= L
        ensures 
            modmul(omega_nk(n, k1), omega_nk(n, k2))
                ==
            omega_nk(n, k1 + k2);
    {
        calc == {
            modmul(omega_nk(n, k1), omega_nk(n, k2));
            ((Pow(omega_n(n), k1) % Q) * (Pow(omega_n(n), k2) % Q)) % Q;
            {
               LemmaMulModNoopGeneral(Pow(omega_n(n), k1), Pow(omega_n(n), k2), Q);
            }
            (Pow(omega_n(n), k1) * Pow(omega_n(n), k2)) % Q;
            {
                LemmaPowAdds(omega_n(n), k1, k2);
            }
            Pow(omega_n(n), k1 + k2) % Q;
        }
    }

    lemma omega_nk_square(n: pow2_t, k: nat)
        requires n.exp <= L
        ensures 
            modmul(omega_nk(n, k), omega_nk(n, k))
                ==
            omega_nk(n, 2 * k);
    {
        omega_nk_mul_lemma(n, k, k);
    }

    lemma ntt_zero_lemma(n: pow2_t)
        requires n.exp <= L;
        ensures omega_nk(n, n.full) == 1;
        decreases n.exp;
    {
        pow2_basics(n);

        if n.exp == 0 {
            calc {
                omega_nk(n, n.full);
                omega_nk(n, 1);
                {
                    LemmaPow1Auto();
                }
                omega_n(n) % Q;
                (Pow(G, Pow2(L - n.exp)) % Q) %Q;
                {
                    LemmaModBasicsAuto();
                }
                Pow(G, Pow2(L - n.exp)) % Q;
                Pow(G, Pow2(L)) % Q;
                {
                    nth_root_lemma();
                }
                1;
            }
            return;
        }
    
        var n' := pow2_half(n);

        assert n'.full == n.full / 2;

        calc {
            omega_nk(n, n.full);
            {
                ntt_cancellation_lemma(n, n'.full);
            }
            omega_nk(n', n'.full);
            {
                ntt_zero_lemma(n');
            }
            1;
        }
    }

    lemma ntt_neg_one_lemma(n: pow2_t)
        requires 1 <= n.exp <= L;
        requires n.full % 2 == 0;
        ensures omega_nk(n, n.full / 2) == Q - 1;
        decreases n.exp
    {
        if n.exp == 1 {
            pow2_basics(n);
            assert n.full == 2;
            calc == {
                omega_nk(n, 1);
                Pow(omega_n(n), 1) % Q;
                {
                    LemmaPow1(omega_n(n)); 
                }
                omega_n(n) % Q;
                (Pow(G, Pow2(L - n.exp)) % Q) % Q;
                {
                    LemmaModBasicsAuto();
                }
                Pow(G, Pow2(L - 1)) % Q;
                Pow(G, Pow2(10)) % Q;
                {
                    reveal Pow();
                    assert Pow2(10) == 1024;
                }
                Pow(G, 1024) % Q;
                {
                    nth_root_lemma();
                }
                Q - 1;
            }
            return;
        }

        var k := n.full / 2;
        var n' := pow2_half(n);

        pow2_basics(n');
        
        calc == {
            omega_nk(n, k);
            {
                ntt_cancellation_lemma(n, n'.full / 2);
            }
            omega_nk(n', n'.full / 2);   
            {
                ntt_neg_one_lemma(n');
            }
            Q-1;
        }
    }

    lemma ntt_halving_lemma(n: pow2_t, k: nat)
        requires 1 <= n.exp <= L
        ensures omega_nk(n, 2 * k + n.full)
                ==
            omega_nk(n, 2 * k);
    {
        var x0 := omega_nk(n, k + n.full / 2);
        var xx0 := modmul(x0, x0);

        var x1 := omega_nk(n, k);
        var xx1 := modmul(x1, x1);

        pow2_basics(n);

        omega_nk_square(n, k + n.full / 2);
        assert xx0 == omega_nk(n, 2 * k + n.full);

        omega_nk_square(n, k);
        assert xx1 == omega_nk(n, 2 * k);

        calc == {
            omega_nk(n, 2 * k + n.full);
            {
                omega_nk_mul_lemma(n, 2 * k, n.full);
            }
            modmul(omega_nk(n, 2 * k), omega_nk(n, n.full));
            {
                ntt_zero_lemma(n);
            }
            omega_nk(n, 2 * k) % Q;
            {
                LemmaModBasicsAuto();
            }
            omega_nk(n, 2 * k);
        }
    }

    lemma mod_pow_cancel(b: nat, e: nat)
        decreases e
        ensures IsModEquivalent(Pow(b, e), Pow(b % Q, e), Q)
    {
        if e == 0 {
            reveal Pow();
            return;
        }
    
        assert IsModEquivalent(Pow(b, e-1), Pow(b % Q, e-1), Q) by {
            mod_pow_cancel(b, e-1);
        }

        assert IsModEquivalent(Pow(b, e-1) * b, Pow(b, e), Q) by {
            reveal Pow();
        }

        assert IsModEquivalent(Pow(b % Q, e), Pow(b % Q, e-1) * (b % Q), Q) by {
            reveal Pow();
        }

        assert IsModEquivalent(Pow(b, e-1) * b, Pow(b % Q, e-1) * b, Q) by {
            LemmaModMulEquivalentAuto();
        }

        assert IsModEquivalent(Pow(b % Q, e-1) * b, Pow(b % Q, e-1) * (b % Q), Q) by {
            assert IsModEquivalent(b, (b % Q), Q) by {
                LemmaModBasicsAuto();
            }
            LemmaModMulEquivalent(b, (b % Q), Pow(b % Q, e-1), Q);
        }
    }

    lemma omega_nk_canonical(n: pow2_t, k: nat)
        requires n.exp <= L
        ensures Pow2(L - n.exp) * k >= 0;   
        ensures omega_nk(n, k) == Pow(G, Pow2(L - n.exp) * k) % Q;
    {
        var om_nk := omega_nk(n, k);
        var temp := Pow(G, Pow2(L - n.exp));
        LemmaPowPositiveAuto();

        assert IsModEquivalent(Pow(temp, k), Pow(temp % Q, k), Q) by {
            mod_pow_cancel(temp, k);
        }

        calc == {
            om_nk;
            Pow(omega_n(n), k) % Q;
            Pow(temp % Q, k) % Q;
            {
                mod_pow_cancel(temp, k);
            }
            Pow(temp, k) % Q;
            Pow(Pow(G, Pow2(L - n.exp)), k) % Q;
            {
                LemmaPowMultiplies(G, Pow2(L - n.exp), k);
            }
            Pow(G, Pow2(L - n.exp) * k) % Q;
        }

        assert Pow2(L - n.exp) * k >= 0 by {
            LemmaMulStrictlyPositiveAuto();
        }
    }
}