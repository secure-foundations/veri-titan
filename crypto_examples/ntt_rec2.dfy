include "ntt_rec.dfy"

module ntt_recs2 {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul
    import opened pows_of_2
    import opened omegas
    import opened rindex
    import opened ntt_rec

    lemma ntt_rec2_base_case_correct(a: seq<elem>, len: pow2_t, idxs: seq<index_t>, ki: nat) 
        requires len.full == 2 && len.exp == 1;
        requires ki < pow2_div(pow2(L), len).full;
        requires ntt_indicies_inv(a, idxs, len, ki); 

        ensures 
            var a_e := [Ar()[ki * len.full]];
            var a_o := [Ar()[ki * len.full + 1]];
            && a_e == even_indexed_terms(a, len)
            && a_o == odd_indexed_terms(a, len)
            && poly_eval_all_points(a_e, a_e, pow2_half(len))
            && poly_eval_all_points(a_o, a_o, pow2_half(len))
    {
        var len' := pow2_half(len);
        pow2_basics(len');

        ntt_indicies_inv_consequence(a, idxs, len, ki);

        var a_e := [Ar()[ki * len.full]];
        var a_o := [Ar()[ki * len.full + 1]];

        calc == {
            a_e[0];
            Ar()[ki * len.full];
            A()[idxs[0].v];
            a[0];
            even_indexed_terms(a, len)[0];
        }

        calc == {
            a_o[0];
            Ar()[ki * len.full + 1];
            A()[idxs[1].v];
            a[1];
            odd_indexed_terms(a, len)[0];
        }

        assert a_e[0] == poly_eval(a_e, omega_nk(len', 0)) by {
            assert a_e[0] == a[0];
            ntt_rec_base_case(a_e, len');
        }
        assert a_o[0] == poly_eval(a_o, omega_nk(len', 0)) by {
            assert a_o[0] == a[1];
            ntt_rec_base_case(a_o, len');
        }
    
        reveal poly_eval_all_points();
    }

    function method ntt_rec2_base(ghost a: seq<elem>, len: pow2_t, ghost idxs: seq<index_t>, ki: nat) : (y: seq<elem>)
        requires len.full == 2 && len.exp == 1;
        requires ki < pow2_div(pow2(L), len).full;
        requires ntt_indicies_inv(a, idxs, len, ki);
        ensures poly_eval_all_points(a, y, len);
    {
        ntt_rec2_base_case_correct(a, len, idxs, ki);

        var a_e := [Ar()[ki * len.full]];
        var a_o := [Ar()[ki * len.full + 1]];

        var y_ks := compute_y_k(a, a_e, a_o, len, 0);
        var y_k's := compute_y_k'(a, a_e, a_o, len, 0);

        assert poly_eval_all_points(a, [y_ks, y_k's], len) by {
            reveal poly_eval_all_points();
        }

        [y_ks, y_k's]
    }

    function method ntt_rec2_combine(ghost a: seq<elem>,
        ghost a_e: seq<elem>,
        ghost a_o: seq<elem>,
        len: pow2_t,
        ghost idxs: seq<index_t>,
        y_e: seq<elem>,
        y_o: seq<elem>,
        ki: nat): (y: seq<elem>)
        requires 2 <= len.full;
        requires len.exp <= L;
        requires ntt_indicies_inv(a, idxs, len, ki); 
        requires ki < pow2_div(pow2(L), len).full;
        requires a_e == even_indexed_terms(a, len);
        requires a_o == odd_indexed_terms(a, len);
        requires poly_eval_all_points(a_e, y_e, pow2_half(len));
        requires poly_eval_all_points(a_o, y_o, pow2_half(len));
        ensures poly_eval_all_points(a, y, len);
    {
        reveal poly_eval_all_points();
        var len' := pow2_half(len);

        var y_ks := compute_y_ks(a, y_e, y_o, len);
        var y_k's := compute_y_k's(a, y_e, y_o, len);
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

    function method ntt_rec2(ghost a: seq<elem>, len: pow2_t, ghost idxs: seq<index_t>, ki: nat) : (y: seq<elem>)
        requires 2 <= len.full;
        requires len.exp <= L;
        requires ki < pow2_div(pow2(L), len).full;
        requires ntt_indicies_inv(a, idxs, len, ki); 
        ensures poly_eval_all_points(a, y, len);
        decreases len.full
    {
        if len.full == 2 then 
            pow2_basics(len);
            ntt_rec2_base(a, len, idxs, ki)
        else
            var len' := pow2_half(len);
            ghost var a_e := even_indexed_terms(a, len);
            ghost var a_o := odd_indexed_terms(a, len);

            ghost var idx_e := even_indexed_indices(idxs, len);
            ghost var idx_o := odd_indexed_indices(idxs, len);

            even_indexed_indices_reorder(a, idxs, len, a_e, idx_e, ki);
            odd_indexed_indices_reorder(a, idxs, len, a_o, idx_o, ki);

            var y_e := ntt_rec2(a_e, len', idx_e, 2 * ki);
            var y_o := ntt_rec2(a_o, len', idx_o, 2 * ki + 1);

            ntt_rec2_combine(a, a_e, a_o, len, idxs, y_e, y_o, ki)
    }

    predicate ntt_chunk_indicies_inv(a: seq<seq<elem>>, idxs: seq<seq<index_t>>, len: pow2_t)
    {
        && 0 <= len.exp <= L
        && |a| == |idxs| == pow2_div(pow2(L), len).full
        && (forall ki: nat | ki < |a| :: (
            && ntt_indicies_inv(a[ki], idxs[ki], len, ki)
            && |a[ki]| == |a[ki]| == len.full))
    }

    predicate ntt_chunks_eval_inv(a: seq<seq<elem>>, idxs: seq<seq<index_t>>, ys: seq<seq<elem>>, len: pow2_t)
    {
        && ntt_chunk_indicies_inv(a, idxs, len)
        && |ys| == pow2_div(pow2(L), len).full
        && (forall ki: nat | ki < |a| ::(
            && |ys[ki]| == len.full
            && poly_eval_all_points(a[ki], ys[ki], len)))
    }

    function method ntt_rec2_chunk_base(ghost a: seq<seq<elem>>, len: pow2_t, ghost idxs: seq<seq<index_t>>): (ys: seq<seq<elem>>)
        requires ntt_chunk_indicies_inv(a, idxs, len);
        requires len.full == 2 && len.exp == 1;
        ensures ntt_chunks_eval_inv(a, idxs, ys, len);
    {
        var num_chunks := pow2_div(pow2(L), len).full;
        var ys := seq(num_chunks, i requires 0 <= i < num_chunks => ntt_rec2_base(a[i], len, idxs[i], i));
        ys
    }

    lemma ntt_rec2_chunk_combine_feasible(
        a: seq<seq<elem>>,
        a': seq<seq<elem>>,
        len: pow2_t,
        count: nat,
        count': nat, 
        idxs: seq<seq<index_t>>,
        idxs': seq<seq<index_t>>,
        ys': seq<seq<elem>>)

        requires 2 <= len.full;
        requires 1 <= len.exp <= L;
        requires count == pow2_div(pow2(L), len).full;
        requires count' == pow2_div(pow2(L), pow2_half(len)).full;
        requires count' == pow2_div(pow2(L), len).full * 2;
        requires ntt_chunk_indicies_inv(a, idxs, len);
        requires a' == seq(count', i  requires 0 <= i < count' => 
                if i % 2 == 0 then even_indexed_terms(a[i/2], len)
                else odd_indexed_terms(a[i/2], len));
        requires idxs' == seq(count', i  requires 0 <= i < count' => 
                if i % 2 == 0 then even_indexed_indices(idxs[i/2], len)
                else odd_indexed_indices(idxs[i/2], len));
        requires ntt_chunks_eval_inv(a', idxs', ys', pow2_half(len));
        ensures forall i |  0 <= i < count ::
            ntt_rec2_combine.requires(a[i], a'[2 * i], a'[2 * i + 1], len, idxs[i], ys'[i * 2], ys'[i * 2 + 1], i);
    {
        var len' := pow2_half(len);

        forall i |  0 <= i < count
            ensures ntt_rec2_combine.requires(a[i], a'[2 * i], a'[2 * i + 1], len, idxs[i], ys'[i * 2], ys'[i * 2 + 1], i);
        {
            var ai := a[i];
            var a_e := a'[2 * i];
            var a_o := a'[2 * i + 1];
            assert a_e == even_indexed_terms(ai, len);
            assert a_o == odd_indexed_terms(ai, len);

            var y_e := ys'[i * 2];
            var y_o := ys'[i * 2 + 1];
    
            assert poly_eval_all_points(a_e, y_e, len');
            assert poly_eval_all_points(a_o, y_o, len');

            assert ntt_rec2_combine.requires(ai, a_e, a_o, len, idxs[i], y_e, y_o, i);
        }
    }

    function method ntt_rec2_chunk_rec(ghost a: seq<seq<elem>>, len: pow2_t, ghost idxs: seq<seq<index_t>>): (ys: seq<seq<elem>>)
        requires ntt_chunk_indicies_inv(a, idxs, len);
        requires 2 <= len.full;
        requires 1 <= len.exp <= L;
        ensures ntt_chunks_eval_inv(a, idxs, ys, len);
        decreases len.exp;
    {
        pow2_basics(len);
        if len.full == 2 then 
            ntt_rec2_chunk_base(a, len, idxs)
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
            var ys' := ntt_rec2_chunk_rec(a', len', idxs');

            ntt_rec2_chunk_combine_feasible(a, a', len, count, count', idxs, idxs', ys');

            var ys := seq(count, i  requires 0 <= i < count => 
                ntt_rec2_combine(a[i], a'[2 * i], a'[2 * i + 1], len, idxs[i], ys'[i * 2], ys'[i * 2 + 1], i));
            ys
    }

}

