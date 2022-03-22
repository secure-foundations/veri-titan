include "pow2.dfy"

module ntt {
    import opened Power
    import opened DivMod
    import opened Mul
    import opened pows_of_2

    const G: nat := 7 // 256-th root of unity
    const Q: nat := 12289

    type elem = i :nat | i < Q

    function method omega_n(n: pow2_t): elem
        requires n.exp <= 8
    {
        Pow(G, Pow2(8 - n.exp)) % Q
    }

    function method omega_nk(n: pow2_t, k: nat): elem
        requires n.exp <= 8
    {
        Pow(omega_n(n), k) % Q
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
        requires n.exp <= 8
        ensures Pow2(8 - n.exp) * k >= 0;   
        ensures omega_nk(n, k) == Pow(G, Pow2(8 - n.exp) * k) % Q;
    {
        var om_nk := omega_nk(n, k);
        var temp := Pow(G, Pow2(8 - n.exp));
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
            Pow(Pow(G, Pow2(8 - n.exp)), k) % Q;
            {
                LemmaPowMultiplies(G, Pow2(8 - n.exp), k);
            }
            Pow(G, Pow2(8 - n.exp) * k) % Q;
        }

        assert Pow2(8 - n.exp) * k >= 0 by {
            LemmaMulStrictlyPositiveAuto();
        }
    }

    lemma cancellation_lemma(n: pow2_t, k: nat)
        requires n.exp != 0;
        requires n.exp <= 8
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

    function poly_eval(a: seq<elem>, x: elem): elem
    // {
    //     if |a| == 0
    //         then 0
    //     else
    //         modadd(modpow(First(a), x), modmul(poly_eval(DropFirst(a), x), x))
    // }

    lemma poly_eval_split_lemma(a: seq<elem>, 
        a_e: seq<elem>, a_o: seq<elem>, len': pow2_t, x: elem)
        requires |a| == len'.full * 2;
        requires a_e ==
            seq(len'.full, n requires 0 <= n < len'.full => a[n * 2]);
        requires a_o == 
            seq(len'.full, n requires 0 <= n < len'.full => a[n * 2 + 1]);
        ensures var sqr := modmul(x, x);
            poly_eval(a, x)
                == 
            modadd(poly_eval(a_e, sqr), modmul(x, poly_eval(a_o, sqr)));

    predicate poly_eval_all_points(a: seq<elem>, y: seq<elem>, len: pow2_t)
        requires 0 <= len.exp <= 8
    {
        && |y| == |a| == len.full
        && (forall i: nat :: i < len.full ==>
            y[i] == poly_eval(a, omega_nk(len, i)))
    }

    // lemma y_k_correct(a: seq<elem>,
    //     logn: nat,
    //     a_e: seq<elem>, a_o: seq<elem>, len': nat,
    //     omg_n: elem, omg_n': elem, k: nat,
    //     y_e_k: elem, y_o_k: elem, y_k: elem)

    //     requires |a| == len' * 2;
    //     requires |a| == Pow2(logn);
    //     requires k < len';
    //     requires a_e == seq(len', n requires 0 <= n < len' => a[n * 2]);
    //     requires a_o == seq(len', n requires 0 <= n < len' => a[n * 2 + 1]);
    //     requires logn <= 8
    //     requires omg_n == modpow(G, Pow2(8 - logn))
    //     requires omg_n' == modpow(G, Pow2(8 - logn + 1))

    //     requires y_e_k == poly_eval(a_e, modpow(omg_n', k));
    //     requires y_o_k == poly_eval(a_o, modpow(omg_n', k));
    //     requires y_k == modadd(y_e_k, modmul(modpow(omg_n, k), y_o_k));
    // {
    //     var sqr := modmul(modpow(omg_n, k), modpow(omg_n, k));
        
    //     calc == {
    //         poly_eval(a, modpow(omg_n, k));
    //         {
    //             poly_eval_split_lemma(a, a_e, a_o, len', modpow(omg_n, k));
    //         }
    //         modadd(poly_eval(a_e, sqr), modmul(modpow(omg_n, k), poly_eval(a_o, sqr)));

    //     }

    //     // modadd(poly_eval(a_e, sqr), modmul(x, poly_eval(a_o, sqr)));
    // }

    lemma ntt_base_case(a: seq<elem>, len: pow2_t)
        requires len.full == 1;
        requires |a| == len.full;
        ensures len.exp == 0;
        ensures a[0] == poly_eval(a, omega_nk(len, 0));
    {
        pow2_basics(len);
        assert len.exp == 0;

        calc {
            poly_eval(a, omega_nk(len, 0));
            {
                omega_nk_canonical(len, 0);
                assert omega_nk(len, 0) == 
                    Pow(G, Pow2(8 - len.exp) * 0) % Q;
            }
            poly_eval(a, Pow(G, Pow2(8 - len.exp) * 0) % Q);
            poly_eval(a, Pow(G, 0) % Q);
            {
                LemmaPow0(G);
            }
            poly_eval(a, 1);
            {
                assume false; // TODO
            }
            a[0];
        }

    }

    method ntt(a: seq<elem>, len: pow2_t) returns (y: seq<elem>)
        requires 1 <= len.full;
        requires len.exp <= 8;
        requires |a| == len.full;
        ensures poly_eval_all_points(a, y, len)
        decreases len.full
    {
        if len.full == 1 {
            ntt_base_case(a, len);
            return a;
        }

        var len' := pow2_half(len);
        var a_e := seq(len'.full, n requires 0 <= n < len'.full => a[n * 2]);
        var a_o := seq(len'.full, n requires 0 <= n < len'.full => a[n * 2 + 1]);

        var y_e := ntt(a_e, len');
        // assert 
        var y_o := ntt(a_o, len');

        y := seq(len.full, n requires 0 <= n < len.full => 0);

        var omgn := omega_n(len);
        var omg := 1;
        var k := 0;

        while (k < len'.full)
            invariant |y| == len.full;
            // invariant 
            decreases len'.full - k;
        {
            var y_e_k := y_e[k];
            var y_o_k := y_o[k];

            assert y_e_k == poly_eval(a_e, omega_nk(len', k));
            assert y_o_k == poly_eval(a_o, omega_nk(len', k));

            var y_k := modadd(y_e_k, modmul(omg, y_o_k));
            y := y[k := y_k];

            var y_k' := modsub(y_e_k, modmul(omg, y_o_k));
            y := y[k + len'.full := y_k'];

            omg := modmul(omg, omgn);
            k := k + 1;
        }
        assume false;
    }
}

