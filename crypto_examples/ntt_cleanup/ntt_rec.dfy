include "polys.dfy"

module ntt_recs {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul
    import opened pows_of_2
    import opened omegas
    import opened rindex
    import opened polys

    lemma y_k_value_lemma(a: seq<elem>,
        len': pow2_t, len: pow2_t,
        omg: elem, k: nat,
        y_e_k: elem, y_o_k: elem, y_k: elem)

        requires |a| == len'.full * 2;
        requires 1 <= len.exp <= L;
        requires len'.exp <= L 
        requires len' == pow2_half(len);

        requires omg == omega_nk(len, k);
        requires y_e_k == poly_eval(even_indexed_terms(a, len), omega_nk(len', k));
        requires y_o_k == poly_eval(odd_indexed_terms(a, len), omega_nk(len', k));
        requires y_k == modadd(y_e_k, modmul(omg, y_o_k));
        
        ensures y_k == poly_eval(a, omega_nk(len, k));
    {
        var x := omega_nk(len, k);
        var sqr := modmul(x, x);

        var a_e := even_indexed_terms(a, len);
        var a_o := odd_indexed_terms(a, len);

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
                poly_eval_split_lemma(a, a_e, a_o, len, x);
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

    lemma y_k'_value_lemma(a: seq<elem>,
        len': pow2_t, len: pow2_t,
        omg: elem, k: nat,
        y_e_k: elem, y_o_k: elem, y_k': elem)

        requires |a| == len'.full * 2;
        requires 1 <= len.exp <= L;
        requires len'.exp <= L 
        requires len' == pow2_half(len);

        requires omg == omega_nk(len, k);
        requires y_e_k == poly_eval(even_indexed_terms(a, len), omega_nk(len', k));
        requires y_o_k == poly_eval(odd_indexed_terms(a, len), omega_nk(len', k));
        requires y_k' == modsub(y_e_k, modmul(omg, y_o_k));

        ensures y_k' == poly_eval(a, omega_nk(len, k + len'.full));
    {
        var x := omega_nk(len, k + len'.full);
        var a_e := even_indexed_terms(a, len);
        var a_o := odd_indexed_terms(a, len);
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
                poly_eval_split_lemma(a, a_e, a_o, len, x);
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
            (y_e_k + (- (omg as int) % Q) * y_o_k) % Q;
            {
                assert y_o_k % Q == y_o_k;
            }
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

    function method compute_y_k(ghost a: seq<elem>,
        y_e: seq<elem>, y_o: seq<elem>,
        len: pow2_t, k: nat): (y_k: elem)
        requires len.exp <= L;
        requires 1 < |a| == len.full;
        requires k < pow2_half(len).full;
        requires poly_eval_all_points(even_indexed_terms(a, len), y_e, pow2_half(len));
        requires poly_eval_all_points(odd_indexed_terms(a, len), y_o, pow2_half(len));
        ensures y_k == poly_eval(a, omega_nk(len, k));
    {
        var len' := pow2_half(len);
        var y_e_k := y_e[k];
        var y_o_k := y_o[k];
        ghost var a_e := even_indexed_terms(a, len);
        ghost var a_o := odd_indexed_terms(a, len);

        var omg := modpow(omega_n(len), k);
        assert y_e_k == poly_eval(a_e, omega_nk(len', k)) by  {
            reveal poly_eval_all_points();
        }
        assert y_o_k == poly_eval(a_o, omega_nk(len', k)) by  {
            reveal poly_eval_all_points();
        }
        var r := modadd(y_e_k, modmul(omg, y_o_k));

        y_k_value_lemma(a, len', len, 
            omg, k, y_e_k, y_o_k, r);

        r
    }

    function method compute_y_ks(ghost a: seq<elem>, 
        y_e: seq<elem>, y_o: seq<elem>,
        len: pow2_t): (a': seq<elem>)
        requires len.exp <= L;
        requires 1 < |a| == len.full;
        requires poly_eval_all_points(even_indexed_terms(a, len), y_e, pow2_half(len));
        requires poly_eval_all_points(odd_indexed_terms(a, len), y_o, pow2_half(len));
        ensures |a'| == pow2_half(len).full;
        ensures forall i: nat | i < |a'| :: a'[i] == poly_eval(a, omega_nk(len, i));
    {
        var half := pow2_half(len).full;
        seq(half, i requires 0 <= i < half => 
            compute_y_k(a, y_e, y_o, len, i))
    }

    function method compute_y_k'(ghost a: seq<elem>,
        y_e: seq<elem>, y_o: seq<elem>,
        len: pow2_t, k: nat): (y_k: elem)
        requires len.exp <= L;
        requires 1 < |a| == len.full;
        requires k < pow2_half(len).full;
        requires poly_eval_all_points(even_indexed_terms(a, len), y_e, pow2_half(len));
        requires poly_eval_all_points(odd_indexed_terms(a, len), y_o, pow2_half(len));
        ensures y_k == poly_eval(a, omega_nk(len, k + pow2_half(len).full));
    {
        var len' := pow2_half(len);
        var y_e_k := y_e[k];
        var y_o_k := y_o[k];
        ghost var a_e := even_indexed_terms(a, len);
        ghost var a_o := odd_indexed_terms(a, len);
    
        var omg := modpow(omega_n(len), k);
        assert y_e_k == poly_eval(a_e, omega_nk(len', k)) by  {
            reveal poly_eval_all_points();
        }
        assert y_o_k == poly_eval(a_o, omega_nk(len', k)) by  {
            reveal poly_eval_all_points();
        }

        var r := modsub(y_e_k, modmul(omg, y_o_k));

        y_k'_value_lemma(a, len', len, 
            omg, k, y_e_k, y_o_k, r);

        r
    }
    
    function method compute_y_k's(ghost a: seq<elem>, 
        y_e: seq<elem>, y_o: seq<elem>,
        len: pow2_t): (a': seq<elem>)
        requires len.exp <= L;
        requires 1 < |a| == len.full;
        requires poly_eval_all_points(even_indexed_terms(a, len), y_e, pow2_half(len));
        requires poly_eval_all_points(odd_indexed_terms(a, len), y_o, pow2_half(len));
        ensures |a'| == pow2_half(len).full;
        ensures forall i: nat | i < |a'| :: a'[i] == poly_eval(a, omega_nk(len, i + pow2_half(len).full));
    {
        var half := pow2_half(len).full;
        seq(half, i requires 0 <= i < half => 
            compute_y_k'(a, y_e, y_o, len, i))
    }

    lemma omg_inv_lemma(omgn: elem, omg: elem, len: pow2_t, k: nat)
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

    lemma ntt_rec_base_case_lemma(a: seq<elem>, len: pow2_t)
        requires len.full == 1;
        requires |a| == len.full;
        ensures len.exp == 0;
        ensures a[0] == poly_eval(a, omega_nk(len, 0));
        ensures poly_eval_all_points(a, a, len)
    {
        pow2_basics(len);
        reveal poly_eval_all_points();
        
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

    function method chunk_count(m: pow2_t): nat
        requires 0 <= m.exp <= L;
    {
        pow2_div(pow2(L), m).full
    }

    lemma chunk_count_half(m: pow2_t)
        requires 1 <= m.exp <= L;
        ensures chunk_count(pow2_half(m)) == chunk_count(m) * 2;
    {
        nth_root_lemma();
        var left := pow2_div(pow2(L), pow2_half(m));
        assert left.full * (m.full / 2) == N;
        var right := pow2_div(pow2(L), m);
        var half := m.full / 2;
        pow2_basics(m);

        calc == {
            left.full * half;
            left.full * (m.full / 2);
            right.full * (2 * half);
            {
                LemmaMulIsAssociativeAuto();
            }
            (right.full * 2) * half;
        }

        LemmaMulEqualityConverse(half, left.full, right.full * 2);
    }

    predicate ntt_rec_combine_enable(a: seq<elem>,
        len: pow2_t,
        idxs: seq<index_t>,
        y_e: seq<elem>,
        y_o: seq<elem>,
        ki: nat)
    {
        && 2 <= len.full
        && len.exp <= L
        && ntt_indicies_inv(a, idxs, len, ki)
        && ki < chunk_count(len)
        && poly_eval_all_points(even_indexed_terms(a, len), y_e, pow2_half(len))
        && poly_eval_all_points(odd_indexed_terms(a, len), y_o, pow2_half(len))
    }

    function method ntt_rec_combine(ghost a: seq<elem>,
        len: pow2_t,
        ghost idxs: seq<index_t>,
        y_e: seq<elem>,
        y_o: seq<elem>,
        ki: nat): (y: seq<elem>)
        requires ntt_rec_combine_enable(a, len, idxs, y_e, y_o, ki);
        ensures poly_eval_all_points(a, y, len);
    {
        var len' := pow2_half(len);

        var y_ks := compute_y_ks(a, y_e, y_o, len);
        var y_k's := compute_y_k's(a, y_e, y_o, len);
        var y := y_ks + y_k's;

        assert poly_eval_all_points(a, y, len) by {
            reveal poly_eval_all_points();
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

    datatype level_view = level_cons(
        ghost a: seq<seq<elem>>,
        ghost idxs: seq<seq<index_t>>,
        m: pow2_t)
    {
        predicate valid_level_view()
        {
            && 0 <= m.exp <= L
            && |a| == |idxs| == chunk_count(m)
            && (forall ki: nat | ki < |a| :: (
                ntt_indicies_inv(a[ki], idxs[ki], m, ki)))
        }

        predicate level_eval(ys: seq<seq<elem>>)
            requires valid_level_view()
        {
            && |ys| == chunk_count(m)
            && (forall ki: nat | ki < |ys| :: (
                && |ys[ki]| == m.full
                && poly_eval_all_points(a[ki], ys[ki], m)))
        }

        function method ntt_rec_base(): (ys: seq<seq<elem>>)
            requires valid_level_view()
            requires m.full == 1 && m.exp == 0;
            ensures level_eval(ys)
        {
            nth_root_lemma();
            var ys := seq(N, i requires 0 <= i < N => [Ar()[i]]);
            assert level_eval(ys) by {
                forall ki: nat | ki < |a| 
                    ensures poly_eval_all_points(a[ki], ys[ki], m)
                {
                    ntt_indicies_inv_consequence0(a[ki], idxs[ki], m, ki);
                    ntt_rec_base_case_lemma(a[ki], m);
                    assert a[ki] == ys[ki];
                }
            }
            ys
        }

        function method {:opaque} build_lower_level(): (lower: level_view)
            requires valid_level_view();
            requires m.exp >= 1;
            ensures lower.valid_level_view();
            ensures lower.m == pow2_half(m);
            ensures chunk_count(lower.m) == 2 * chunk_count(m);
        {
            var m' := pow2_half(m);
            var count' := chunk_count(m');
            chunk_count_half(m);

            ghost var a' := seq(count', i  requires 0 <= i < count' => 
                if i % 2 == 0 then even_indexed_terms(a[i/2], m)
                else odd_indexed_terms(a[i/2], m));

            ghost var idxs' := seq(count', i  requires 0 <= i < count' => 
                if i % 2 == 0 then even_indexed_indices(idxs[i/2], m)
                else odd_indexed_indices(idxs[i/2], m));

            var lower := level_cons(a', idxs', m');

            assert lower.valid_level_view() by {
                forall i | 0 <= i < count'
                    ensures ntt_indicies_inv(a'[i], idxs'[i], m', i);
                {
                    var ki := i/2;

                    var ai: seq<elem> := a[i/2];
                    var idx := idxs[i/2];
        
                    assert ntt_indicies_inv(a[ki], idxs[ki], m, ki);
    
                    if i % 2 == 0 {
                        ghost var a_e := even_indexed_terms(ai, m);
                        ghost var idx_e := even_indexed_indices(idx, m);
                        even_indexed_indices_reorder(ai, idx, m, a_e, idx_e, ki);
                    } else {
                        ghost var a_o := odd_indexed_terms(ai, m);
                        ghost var idx_o := odd_indexed_indices(idx, m);
                        odd_indexed_indices_reorder(ai, idx, m, a_o, idx_o, ki);
                    }
                }
            }

            lower
        }

        function method lower_even_chunk(ys: seq<seq<elem>>, ki: nat): seq<elem>
            requires valid_level_view();
            requires 0 <= ki < chunk_count(m);
            requires |ys| == chunk_count(m) * 2;
        {
            ys[2 * ki]
        }

        function method lower_odd_index(ys: seq<seq<elem>>, ki: nat): seq<elem>
            requires valid_level_view();
            requires 0 <= ki < chunk_count(m);
            requires |ys| == chunk_count(m) * 2;
        {
            assert 2 * ki + 1 < |ys| by {
                calc {
                    2 * ki + 1;
                <=
                    2 * (chunk_count(m) - 1) + 1;
                    2 * chunk_count(m) - 1;
                    |ys| - 1;
                }
            }
            ys[2 * ki + 1]
        }

        lemma ntt_level_terms_correspondence_lemma(lower: level_view, ki: nat)
            requires m.exp >= 1;
            requires valid_level_view();
            requires ki < |a|;
            requires lower == build_lower_level();
            ensures lower.a[ki*2] == even_indexed_terms(a[ki], m);
            ensures lower.a[ki*2+1] == odd_indexed_terms(a[ki], m);
        {
            reveal build_lower_level();
        }

        lemma ntt_rec_chunk_combine_lemma(lower: level_view, ys: seq<seq<elem>>)
            requires m.exp >= 1;
            requires valid_level_view();
            requires lower == build_lower_level();
            requires lower.level_eval(ys);
            requires |ys| == chunk_count(m) * 2;
            ensures forall i |  0 <= i < chunk_count(m) ::
                ntt_rec_combine_enable(a[i], m, idxs[i],
                    lower_even_chunk(ys, i), lower_odd_index(ys, i), i);
        {
            var len := m;
            var len' := pow2_half(m);
            chunk_count_half(m);

            forall i |  0 <= i < chunk_count(m) 
                ensures ntt_rec_combine_enable(a[i], len, idxs[i],
                    lower_even_chunk(ys, i), lower_odd_index(ys, i), i);
            {
                reveal build_lower_level();
                var ai := a[i];
                var a_e := lower.a[2 * i];
                var a_o := lower.a[2 * i + 1];
                assert a_e == even_indexed_terms(ai, len);
                assert a_o == odd_indexed_terms(ai, len);

                var y_e := ys[i * 2];
                var y_o := ys[i * 2 + 1];
        
                assert poly_eval_all_points(a_e, y_e, len');
                assert poly_eval_all_points(a_o, y_o, len');
            }
        }

        function method {:opaque} ntt_rec(): (ys: seq<seq<elem>>)
            requires valid_level_view()
            ensures level_eval(ys)
            decreases m.exp;
        {
            pow2_basics(m);
            if m.full == 1 then 
                ntt_rec_base()
            else
                var lower := build_lower_level();
                var ys' := lower.ntt_rec();
                ntt_rec_chunk_combine_lemma(lower, ys');
                var count := chunk_count(m);

                var ys := seq(count, i  requires 0 <= i < count => 
                    ntt_rec_combine(a[i], m, idxs[i], lower_even_chunk(ys', i), lower_odd_index(ys', i), i));
                ys
        }        
    }

}