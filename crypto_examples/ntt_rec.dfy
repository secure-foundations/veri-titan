include "pow2.dfy"
include "omega.dfy"
include "index.dfy"

module ntt_rec {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul
    import opened pows_of_2
    import opened omegas
    import opened rindex

    function {:opaque} poly_eval(a: seq<elem>, x: elem): elem
    {
        if |a| == 0 then 0
        else modadd(First(a), modmul(poly_eval(DropFirst(a), x), x))
    }

    function method odd_indexed_terms(a: seq<elem>, len: pow2_t): seq<elem>
        requires |a| == len.full * 2;
    {
        seq(len.full, n requires 0 <= n < len.full => a[n * 2 + 1])
    }

    function method even_indexed_terms(a: seq<elem>, len: pow2_t): seq<elem>
        requires |a| == len.full * 2;
    {
        seq(len.full, n requires 0 <= n < len.full => a[n * 2])
    }

    lemma poly_eval_base_lemma(a: seq<elem>, x: elem)
        requires |a| == 1;
        ensures poly_eval(a, x) == a[0];
    {
        reveal poly_eval();
    }

    lemma {:axiom} poly_eval_split_lemma(a: seq<elem>, 
        a_e: seq<elem>, a_o: seq<elem>, len: pow2_t, x: elem)
        requires |a| == len.full * 2;
        requires a_e == even_indexed_terms(a, len)
        requires a_o == odd_indexed_terms(a, len)
        ensures var sqr := modmul(x, x);
            poly_eval(a, x)
                == 
            modadd(poly_eval(a_e, sqr), modmul(x, poly_eval(a_o, sqr)));
        decreases |a|;
    {
        // pow2_basics(len);

        // if |a| == 2 {
        //     assert a_e == [a[0]];
        //     assert a_o == [a[1]];

        //     var sqr := modmul(x, x);

        //     calc == {
        //         poly_eval(a, x);
        //         {
        //             reveal poly_eval();
        //             assert DropFirst(a) == a_o;
        //         }
        //         modadd(a[0], modmul(poly_eval(a_o, x), x));
        //         {
        //             poly_eval_base_lemma(a_o, x);
        //             assert poly_eval(a_o, x) == a[1];
        //         }
        //         modadd(a[0], modmul(a[1], x));
        //         {
        //             poly_eval_base_lemma(a_e, sqr);
        //             assert poly_eval(a_e, sqr) == a[0];
        //         }
        //         modadd(poly_eval(a_e, sqr), modmul(a[1], x));
        //         {
        //             poly_eval_base_lemma(a_o, sqr);
        //             assert poly_eval(a_o, sqr) == a[1];
        //         }
        //         modadd(poly_eval(a_e, sqr), modmul(x, poly_eval(a_o, sqr)));
        //     }
        //     return;
        // }

        // var len' := pow2_half(len);
        // var a_ee := even_indexed_terms(a_e, len');
        // var a_eo := odd_indexed_terms(a_e, len');
        // var a_oe := even_indexed_terms(a_o, len');
        // var a_oo := odd_indexed_terms(a_o, len');

        // calc == {
        //     poly_eval(a, x);
        //     {
        //         reveal poly_eval();
        //         assert DropFirst(a) == a_o;
        //     }
        //     modadd(a[0], modmul(poly_eval(a_o, x), x));
        // }
        assume false;
    }

    predicate poly_eval_all_points(a: seq<elem>, y: seq<elem>, len: pow2_t)
        requires 0 <= len.exp <= L
    {
        && |y| == |a| == len.full
        && (forall i: nat | i < len.full ::
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
        requires a_e == even_indexed_terms(a, len');
        requires a_o == odd_indexed_terms(a, len');

        requires omg == omega_nk(len, k);
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
        requires a_e == even_indexed_terms(a, len');
        requires a_o == odd_indexed_terms(a, len');

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

    lemma ntt_rec_base_case(a: seq<elem>, len: pow2_t)
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
                poly_eval_base_lemma(a, 1);
            }
            a[0];
        }
    }

    // method ntt_rec(a: seq<elem>, len: pow2_t) returns (y: seq<elem>)
    //     // requires len.exp == L ==> a == A();
    //     requires 1 <= len.full;
    //     requires len.exp <= L;
    //     requires |a| == len.full;
    //     ensures poly_eval_all_points(a, y, len)
    //     decreases len.full
    // {
    //     if len.full == 1 {
    //         ntt_rec_base_case(a, len);
    //         return a;
    //     }

    //     var len' := pow2_half(len);
    //     var a_e := even_indexed_terms(a, len');
    //     var a_o := odd_indexed_terms(a, len');

    //     var y_e := ntt_rec(a_e, len');
    //     var y_o := ntt_rec(a_o, len');

    //     y := seq(len.full, n requires 0 <= n < len.full => 0);

    //     var omgn := omega_n(len);
    //     var omg := 1;
    //     var k := 0;

    //     assert omg == modpow(omgn, 0) by {
    //         LemmaPow0Auto();
    //     }

    //     while (k < len'.full)
    //         invariant k <= len'.full;
    //         invariant |y| == len.full;
    //         invariant len.full == len'.full * 2;

    //         invariant omg == modpow(omgn, k);
    //         invariant forall i: nat :: i < k ==> (
    //             && y[i] == poly_eval(a, omega_nk(len, i))
    //             && y[i + len'.full] == poly_eval(a, omega_nk(len, i + len'.full)))
            
    //         decreases len'.full - k;
    //     {
    //         var y_e_k := y_e[k];
    //         var y_o_k := y_o[k];

    //         assert y_e_k == poly_eval(a_e, omega_nk(len', k));
    //         assert y_o_k == poly_eval(a_o, omega_nk(len', k));

    //         var y_k := modadd(y_e_k, modmul(omg, y_o_k));
    //         y := y[k := y_k];

    //         var y_k' := modsub(y_e_k, modmul(omg, y_o_k));
    //         y := y[k + len'.full := y_k'];

    //         y_k_value(a, a_e, a_o, len', len, 
    //             omg, k, y_e_k, y_o_k, y_k);

    //         y_k'_value(a, a_e, a_o, len', len, 
    //             omg, k, y_e_k, y_o_k, y_k');

    //         omg_inv(omgn, omg, len, k);
    //         omg := modmul(omg, omgn);

        
    //         k := k + 1;
    //     }

    //     forall i: nat
    //         ensures i < len.full ==> y[i] == poly_eval(a, omega_nk(len, i))
    //     {
    //         if i < len'.full {
    //             assert y[i] == poly_eval(a, omega_nk(len, i));
    //         } else if i < len.full {
    //             var j := i - len'.full;
    //             assert y[j + len'.full] ==
    //                 poly_eval(a, omega_nk(len, j + len'.full));
    //         }
    //     }
    // }

    function method compute_y_k(a: seq<elem>,
        a_e: seq<elem>, a_o: seq<elem>,
        y_e: seq<elem>, y_o: seq<elem>,
        len: pow2_t, k: nat): (y_k: elem)
        requires len.exp <= L;
        requires 1 < |a| == len.full;
        requires k < pow2_half(len).full;
        requires a_e == even_indexed_terms(a, pow2_half(len));
        requires a_o == odd_indexed_terms(a, pow2_half(len));
        requires poly_eval_all_points(a_e, y_e, pow2_half(len));
        requires poly_eval_all_points(a_o, y_o, pow2_half(len));
        ensures y_k == poly_eval(a, omega_nk(len, k));
    {
        var len' := pow2_half(len);
        var y_e_k := y_e[k];
        var y_o_k := y_o[k];

        var omg := modpow(omega_n(len), k);
        assert y_e_k == poly_eval(a_e, omega_nk(len', k));
        assert y_o_k == poly_eval(a_o, omega_nk(len', k));

        var r := modadd(y_e_k, modmul(omg, y_o_k));

        y_k_value(a, a_e, a_o, len', len, 
            omg, k, y_e_k, y_o_k, r);

        r
    }

    function method compute_y_ks(a: seq<elem>, 
        a_e: seq<elem>, a_o: seq<elem>,
        y_e: seq<elem>, y_o: seq<elem>,
        len: pow2_t): (a': seq<elem>)
        requires len.exp <= L;
        requires 1 < |a| == len.full;
        requires a_e == even_indexed_terms(a, pow2_half(len));
        requires a_o == odd_indexed_terms(a, pow2_half(len));
        requires poly_eval_all_points(a_e, y_e, pow2_half(len));
        requires poly_eval_all_points(a_o, y_o, pow2_half(len));
        ensures |a'| == pow2_half(len).full;
        ensures forall i: nat | i < |a'| :: a'[i] == poly_eval(a, omega_nk(len, i));
    {
        var half := pow2_half(len).full;
        seq(half, i requires 0 <= i < half => 
            compute_y_k(a, a_e, a_o, y_e, y_o, len, i))
    }

    function method compute_y_k'(a: seq<elem>,
        a_e: seq<elem>, a_o: seq<elem>,
        y_e: seq<elem>, y_o: seq<elem>,
        len: pow2_t, k: nat): (y_k: elem)
        requires len.exp <= L;
        requires 1 < |a| == len.full;
        requires k < pow2_half(len).full;
        requires a_e == even_indexed_terms(a, pow2_half(len));
        requires a_o == odd_indexed_terms(a, pow2_half(len));
        requires poly_eval_all_points(a_e, y_e, pow2_half(len));
        requires poly_eval_all_points(a_o, y_o, pow2_half(len));
        ensures y_k == poly_eval(a, omega_nk(len, k + pow2_half(len).full));
    {
        var len' := pow2_half(len);
        var y_e_k := y_e[k];
        var y_o_k := y_o[k];

        var omg := modpow(omega_n(len), k);
        assert y_e_k == poly_eval(a_e, omega_nk(len', k));
        assert y_o_k == poly_eval(a_o, omega_nk(len', k));

        var r := modsub(y_e_k, modmul(omg, y_o_k));

        y_k'_value(a, a_e, a_o, len', len, 
            omg, k, y_e_k, y_o_k, r);

        r
    }
    
    function method compute_y_k's(a: seq<elem>, 
        a_e: seq<elem>, a_o: seq<elem>,
        y_e: seq<elem>, y_o: seq<elem>,
        len: pow2_t): (a': seq<elem>)
        requires len.exp <= L;
        requires 1 < |a| == len.full;
        requires a_e == even_indexed_terms(a, pow2_half(len));
        requires a_o == odd_indexed_terms(a, pow2_half(len));
        requires poly_eval_all_points(a_e, y_e, pow2_half(len));
        requires poly_eval_all_points(a_o, y_o, pow2_half(len));
        ensures |a'| == pow2_half(len).full;
        ensures forall i: nat | i < |a'| :: a'[i] == poly_eval(a, omega_nk(len, i + pow2_half(len).full));
    {
        var half := pow2_half(len).full;
        seq(half, i requires 0 <= i < half => 
            compute_y_k'(a, a_e, a_o, y_e, y_o, len, i))
    }

    function method ntt_rec(a: seq<elem>, len: pow2_t) : (y: seq<elem>)
        requires 1 <= len.full;
        requires len.exp <= L;
        requires |a| == len.full;
        ensures poly_eval_all_points(a, y, len)
        decreases len.full
    {
        if len.full == 1 then 
            ntt_rec_base_case(a, len);
            a
        else
            var len' := pow2_half(len);
            var a_e := even_indexed_terms(a, len');
            var a_o := odd_indexed_terms(a, len');

            var y_e := ntt_rec(a_e, len');
            var y_o := ntt_rec(a_o, len');

            var y_ks := compute_y_ks(a, a_e, a_o, y_e, y_o, len);
            var y_k's := compute_y_k's(a, a_e, a_o, y_e, y_o, len);
            var y := y_ks + y_k's;

            assert forall i: nat | i < len.full ::
                y[i] == poly_eval(a, omega_nk(len, i)) by {
                forall i: nat | i < len.full
                    ensures y[i] == poly_eval(a, omega_nk(len, i))
                {
                    if i < len'.full {
                        assert y[i] == y_ks[i];
                    } else {
                        var j := i - len'.full;
                        assert y[i] == y_k's[j];
                    }
                }
            }
            y
    }
}

