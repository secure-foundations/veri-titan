include "pow2.dfy"
include "omega.dfy"

module ntt {
    import opened Power
    import opened DivMod
    import opened Mul
    import opened pows_of_2
    import opened omegas

    function poly_eval(a: seq<elem>, x: elem): elem
    // {
    //     if |a| == 0
    //         then 0
    //     else
    //         modadd(modpow(First(a), x), modmul(poly_eval(DropFirst(a), x), x))
    // }

    lemma {:axiom} poly_eval_split_lemma(a: seq<elem>, 
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
        requires 0 <= len.exp <= L
    {
        && |y| == |a| == len.full
        && (forall i: nat :: i < len.full ==>
            y[i] == poly_eval(a, omega_nk(len, i)))
    }

    lemma y_k_value(a: seq<elem>,
        a_e: seq<elem>, a_o: seq<elem>,
        len': pow2_t, len: pow2_t,
        omg: elem, k: nat,
        y_e_k: elem, y_o_k: elem, y_k: elem)

        requires |a| == len'.full * 2;
        requires 1 <= len.exp <= L;
        requires len'.exp <= L 
        requires len' == pow2_half(len);
        requires k < len'.full;
        requires a_e == 
            seq(len'.full, n requires 0 <= n < len'.full => a[n * 2]);
        requires a_o ==
            seq(len'.full, n requires 0 <= n < len'.full => a[n * 2 + 1]);

        requires omg == modpow(omega_n(len), k);
        requires y_e_k == poly_eval(a_e, omega_nk(len', k));
        requires y_o_k == poly_eval(a_o, omega_nk(len', k));
        requires y_k == modadd(y_e_k, modmul(omg, y_o_k));
        
        ensures y_k == poly_eval(a, omega_nk(len, k));
    {
        var x := omega_nk(len, k);
        var sqr := modmul(x, x);

        calc == {
            sqr;
            {
                omega_nk_square(len, k);
            }
            omega_nk(len, 2 * k);
            {
                ntt_cancellation_lemma(len, k);
            }
            omega_nk(len', k);
        }

        calc == {
            poly_eval(a, x);
            {
                poly_eval_split_lemma(a, a_e, a_o, len', x);
            }
            modadd(poly_eval(a_e, sqr), modmul(x, poly_eval(a_o, sqr)));
            {
                assert poly_eval(a_e, sqr) == y_e_k;
                assert poly_eval(a_o, sqr) == y_o_k;
            }
            modadd(y_e_k, modmul(x, y_o_k));
            y_k;
        }
    }

    lemma y_k'_value(a: seq<elem>,
        a_e: seq<elem>, a_o: seq<elem>,
        len': pow2_t, len: pow2_t,
        omg: elem, k: nat,
        y_e_k: elem, y_o_k: elem, y_k': elem)

        requires |a| == len'.full * 2;
        requires 1 <= len.exp <= L;
        requires len'.exp <= L 
        requires len' == pow2_half(len);
        requires k < len'.full;
        requires a_e == 
            seq(len'.full, n requires 0 <= n < len'.full => a[n * 2]);
        requires a_o ==
            seq(len'.full, n requires 0 <= n < len'.full => a[n * 2 + 1]);

        requires omg == omega_nk(len, k);
        requires y_e_k == poly_eval(a_e, omega_nk(len', k));
        requires y_o_k == poly_eval(a_o, omega_nk(len', k));
        requires y_k' == modsub(y_e_k, modmul(omg, y_o_k));

        ensures y_k' == poly_eval(a, omega_nk(len, k + len'.full));
    {
        var x := omega_nk(len, k + len'.full);
        var sqr := modmul(x, x);

        calc == {
            sqr;
            {
                omega_nk_square(len, k + len'.full);
            }
            omega_nk(len, 2 * k + len.full);
            {
                ntt_halving_lemma(len, k);
            }
            omega_nk(len, 2 * k);
            {
                ntt_cancellation_lemma(len, k);
            }
            omega_nk(len', k);
        }

        calc {
            x;
            omega_nk(len, k + len'.full);
            {
                omega_nk_mul_lemma(len, k, len'.full);
            }
            modmul(omg, omega_nk(len, len'.full));
            {
                ntt_neg_one_lemma(len);
            }
            modmul(omg, Q - 1);
            (omg * (Q - 1)) % Q;
            {
                LemmaMulIsDistributiveSubAuto();
            }
            (omg * Q - omg) % Q;
            {
                LemmaModMultiplesVanishAuto();
            }
            (- (omg as int)) % Q;
        }

        calc == {
            poly_eval(a, x);
            {
                poly_eval_split_lemma(a, a_e, a_o, len', x);
            }
            modadd(poly_eval(a_e, sqr), modmul(x, poly_eval(a_o, sqr)));
            {
                assert poly_eval(a_e, sqr) == y_e_k;
                assert poly_eval(a_o, sqr) == y_o_k;
            }
            modadd(y_e_k, modmul(x, y_o_k));
            (y_e_k + (x * y_o_k) % Q) % Q;
            {
                LemmaAddModNoopRight(y_e_k, x * y_o_k, Q);
            }
            (y_e_k + x * y_o_k) % Q;
            (y_e_k + (- (omg as int) % Q) * y_o_k ) % Q;
            (y_e_k + (- (omg as int) % Q) * (y_o_k % Q)) % Q;
            {
                LemmaMulModNoopLeft(- (omg as int), y_o_k, Q);
            }
            (y_e_k + ((-(omg as int) * y_o_k) % Q)) % Q;
            {
                LemmaAddModNoopRight(y_e_k, -(omg as int) * y_o_k, Q);
            }
            (y_e_k + (-(omg as int) * y_o_k)) % Q;
            (y_e_k + ((-1 * (omg as int)) * y_o_k)) % Q;
            {
                LemmaMulIsAssociativeAuto();
            }
            (y_e_k - 1 * (omg as int) * y_o_k) % Q;
            {
                LemmaMulBasicsAuto();
            }
            (y_e_k - (omg as int) * y_o_k) % Q;
            (y_e_k - (omg * y_o_k)) % Q;
            {
                LemmaSubModNoopRight(y_e_k, omg * y_o_k, Q);
            }
            (y_e_k - (omg * y_o_k) % Q) % Q;
            modsub(y_e_k, modmul(omg, y_o_k));
            y_k';
        }
    }

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
                    Pow(G, Pow2(L - len.exp) * 0) % Q;
            }
            poly_eval(a, Pow(G, Pow2(L - len.exp) * 0) % Q);
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

    lemma omg_inv(omgn: elem, omg: elem, len: pow2_t, k: nat)
        requires len.exp <= L
        requires omgn == omega_n(len);
        requires omg == modpow(omgn, k);
        ensures modmul(omg, omgn) == modpow(omgn, k+1);
    {
        var omg' := modmul(omg, omgn);
        calc == {
            omg';
            modmul(omg, omgn);
            modmul(modpow(omgn, k), omgn);
            (Pow(omgn, k) % Q * omgn) % Q;
            {
                LemmaMulModNoopLeft(Pow(omgn, k), omgn, Q);
            }
            (Pow(omgn, k) * omgn) % Q;
            {
                LemmaPow1(omgn);
                assert omgn == Pow(omgn, 1);
                LemmaPowAdds(omgn, k, 1);
            }
            Pow(omgn, k+1) % Q;
            modpow(omgn, k+1);
        }
    }

    method ntt_rec(a: seq<elem>, len: pow2_t) returns (y: seq<elem>)
        requires 1 <= len.full;
        requires len.exp <= L;
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

        var y_e := ntt_rec(a_e, len');
        var y_o := ntt_rec(a_o, len');

        y := seq(len.full, n requires 0 <= n < len.full => 0);

        var omgn := omega_n(len);
        var omg := 1;
        var k := 0;

        assert omg == modpow(omgn, 0) by {
            LemmaPow0Auto();
        }

        while (k < len'.full)
            invariant k <= len'.full;
            invariant |y| == len.full;
            invariant len.full == len'.full * 2;

            invariant omg == modpow(omgn, k);
            invariant forall i: nat :: i < k ==> (
                && y[i] == poly_eval(a, omega_nk(len, i))
                && y[i + len'.full] == poly_eval(a, omega_nk(len, i + len'.full)))
            
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

            y_k_value(a, a_e, a_o, len', len, 
                omg, k, y_e_k, y_o_k, y_k);

            y_k'_value(a, a_e, a_o, len', len, 
                omg, k, y_e_k, y_o_k, y_k');

            omg_inv(omgn, omg, len, k);
            omg := modmul(omg, omgn);

            k := k + 1;
        }

        forall i: nat
            ensures i < len.full ==> y[i] == poly_eval(a, omega_nk(len, i))
        {
            if i < len'.full {
                assert y[i] == poly_eval(a, omega_nk(len, i));
            } else if i < len.full {
                var j := i - len'.full;
                assert y[j + len'.full] ==
                    poly_eval(a, omega_nk(len, j + len'.full));
            }
        }
    }


    // method ntt(a: seq<elem>, len: pow2_t) returns (y: seq<elem>)
    //     requires len.full == N;
    // //     requires |a| == 
    // // {

    // // }
    
}

