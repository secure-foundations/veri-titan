include "ntt_rec2.dfy"

module ntt_recs3 {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul
    import opened pows_of_2
    import opened omegas
    import opened rindex
    import opened ntt_recs2
    import opened ntt_rec

    function method chunk_count(m: pow2_t): nat
        requires 0 <= m.exp <= L;
    {
        pow2_div(pow2(L), m).full
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
                && ntt_indicies_inv(a[ki], idxs[ki], m, ki)
                && |a[ki]| == |a[ki]| == m.full))
        }

        predicate level_eval(ys: seq<seq<elem>>)
            requires valid_level_view()
        {
            && |ys| == chunk_count(m)
            && (forall ki: nat | ki < |ys| :: (
                && |ys[ki]| == m.full
                && poly_eval_all_points(a[ki], ys[ki], m)))
        }

        function method ntt_rec3_base(): (ys: seq<seq<elem>>)
            requires valid_level_view()
            requires m.full == 1 && m.exp == 0;
            ensures level_eval(ys)
        {
            nth_root_lemma();
            var ys := seq(N, i requires 0 <= i < N => [Ar()[i]]);
            assert ntt_chunks_eval_inv(a, idxs, ys, m) by {
                forall ki: nat | ki < |a| 
                    ensures poly_eval_all_points(a[ki], ys[ki], m)
                {
                    ntt_indicies_inv_consequence0(a[ki], idxs[ki], m, ki);
                    ntt_rec_base_case(a[ki], m);
                    assert a[ki] == ys[ki];
                }
            }
            ys
        }

        function method ntt_rec3(): (ys: seq<seq<elem>>)
            requires valid_level_view()
            decreases m.exp;
        {
            pow2_basics(m);
            if m.full == 1 then 
                ntt_rec3_base()
            else
                var m' := pow2_half(m);
                var count := chunk_count(m);
                var count' := chunk_count(m');
                assume count' == count * 2;

                ghost var a' := seq(count', i  requires 0 <= i < count' => 
                    if i % 2 == 0 then even_indexed_terms(a[i/2], m)
                    else odd_indexed_terms(a[i/2], m));

                ghost var idxs' := seq(count', i  requires 0 <= i < count' => 
                    if i % 2 == 0 then even_indexed_indices(idxs[i/2], m)
                    else odd_indexed_indices(idxs[i/2], m));

                assert ntt_chunk_indicies_inv(a', idxs', m') by {
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
                var lv' := level_cons(a', idxs', m');
                var ys' := lv'.ntt_rec3();

                ntt_rec2_chunk_combine_feasible(a, a', m, count, count', idxs, idxs', ys');

                var ys := seq(count, i  requires 0 <= i < count => 
                    ntt_rec2_combine(a[i], a'[2 * i], a'[2 * i + 1], m, idxs[i], ys'[i * 2], ys'[i * 2 + 1], i));
                ys
        }        
    }

}