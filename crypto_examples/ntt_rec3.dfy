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

   function method ntt_rec3_base(ghost a: seq<seq<elem>>, len: pow2_t, ghost idxs: seq<seq<index_t>>): (ys: seq<seq<elem>>)
        requires ntt_chunk_indicies_inv(a, idxs, len);
        requires len.full == 1 && len.exp == 0;
        ensures ntt_chunks_eval_inv(a, idxs, ys, len);
    {
        nth_root_lemma();
        var ys := seq(N, i requires 0 <= i < N => [Ar()[i]]);
        assert ntt_chunks_eval_inv(a, idxs, ys, len) by {
            forall ki: nat | ki < |a| 
                ensures poly_eval_all_points(a[ki], ys[ki], len)
            {
                ntt_indicies_inv_consequence0(a[ki], idxs[ki], len, ki);
                ntt_rec_base_case(a[ki], len);
            }
        }
        ys
    }

    function method ntt_rec3(ghost a: seq<seq<elem>>, len: pow2_t, ghost idxs: seq<seq<index_t>>): (ys: seq<seq<elem>>)
        requires ntt_chunk_indicies_inv(a, idxs, len);
        requires 1 <= len.full;
        requires 0 <= len.exp <= L;
        ensures ntt_chunks_eval_inv(a, idxs, ys, len);
        decreases len.exp;
    {
        pow2_basics(len);
        if len.full == 1 then 
            ntt_rec3_base(a, len, idxs)
        else
            var len' := pow2_half(len);
            var count := pow2_div(pow2(L), len).full;
            var count' := pow2_div(pow2(L), len').full;
            assume count' == pow2_div(pow2(L), len).full * 2;

            ghost var a' := seq(count', i  requires 0 <= i < count' => 
                if i % 2 == 0 then even_indexed_terms(a[i/2], len)
                else odd_indexed_terms(a[i/2], len));

            ghost var idxs' := seq(count', i  requires 0 <= i < count' => 
                if i % 2 == 0 then even_indexed_indices(idxs[i/2], len)
                else odd_indexed_indices(idxs[i/2], len));

            assert ntt_chunk_indicies_inv(a', idxs', len') by {
                forall i | 0 <= i < count'
                    ensures ntt_indicies_inv(a'[i], idxs'[i], len', i);
                {
                    var ki := i/2;

                    var ai: seq<elem> := a[i/2];
                    var idx := idxs[i/2];
        
                    assert ntt_indicies_inv(a[ki], idxs[ki], len, ki);
    
                    if i % 2 == 0 {
                        ghost var a_e := even_indexed_terms(ai, len);
                        ghost var idx_e := even_indexed_indices(idx, len);
                        even_indexed_indices_reorder(ai, idx, len, a_e, idx_e, ki);
                    } else {
                        ghost var a_o := odd_indexed_terms(ai, len);
                        ghost var idx_o := odd_indexed_indices(idx, len);
                        odd_indexed_indices_reorder(ai, idx, len, a_o, idx_o, ki);
                    }
                }
            }
            var ys' := ntt_rec3(a', len', idxs');

            ntt_rec2_chunk_combine_feasible(a, a', len, count, count', idxs, idxs', ys');

            var ys := seq(count, i  requires 0 <= i < count => 
                ntt_rec2_combine(a[i], a'[2 * i], a'[2 * i + 1], len, idxs[i], ys'[i * 2], ys'[i * 2 + 1], i));
            ys
    }
}