include "ntt_rec.dfy"

module ntt_rec2 {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul
    import opened pows_of_2
    import opened omegas
    import opened rindex
    import opened ntt_rec

    predicate poly_eval_chunks(ys: seq<seq<elem>>, clen: pow2_t)
        requires 0 <= clen.exp <= L
        requires |A()| == N == pow2(L).full
    {
        && |ys| == pow2_div(pow2(L), clen).full
        && (forall ki: nat, i: nat | ki < |ys| && i < clen.full ::(
            && |ys[ki]| == clen.full
            && clen.full * ki + i >= 0
            && ys[ki][i] == poly_eval(A(), omega_nk(clen, clen.full * ki + i))))
    }

    // lemma ntt_chunks_base_case(clen: pow2_t)
    //     requires clen.exp == 0
    //     ensures poly_eval_chunks(ys, len);

    // lemma ntt_chunks_rec_case(ys': seq<seq<elem>>, k: nat,
    //     ys: seq<seq<elem>>, clen: pow2_t)
    //     requires 1 <= clen.exp <= L
    //     requires k < |ys'| == pow2_div(pow2(L), clen).full
    //     requires |ys'[k]| == clen.full;
    //     requires poly_eval_chunks(ys, pow2_half(clen));
    // {
    //     assume |ys| == 2 * |ys'|;
    //     var y_e := ys[2 * k];
    //     var y_o := ys[2 * k + 1];
    //     compute_y_ks(a: seq<elem>, 
    //     a_e: seq<elem>, a_o: seq<elem>,
    //     y_e, y_o,
    //     len):
    // }

    // function method ntt_rec_chunk_combine()

    // function method {:fuel 1} ntt_rec_chunks(clen: pow2_t): (ys: seq<seq<elem>>)
    //     requires 0 <= clen.exp <= L
    //     ensures poly_eval_chunks(ys, clen);
    //     decreases clen.exp
    // {
    //     if clen.exp == 0 then
    //         var ys := seq(N, i requires 0 <= i < N => [Ar()[i]]);
    //         assume poly_eval_chunks(ys, clen);
    //         ys
    //     else
    //         var ys := ntt_rec_chunks(pow2_half(clen));
    //         var ccount := pow2_div(pow2(L), clen).full;
    //         var ys' := seq(ccount, i requires 0 <= i < ccount => [0]);
    //         assume false;
    //         ys'
    // }

    function method ntt_rec2(a: seq<elem>, len: pow2_t, ghost idxs: seq<index_t>, ghost ki: nat) : (y: seq<elem>)
        requires 2 <= len.full;
        requires len.exp <= L;
        requires |a| == |idxs| == len.full;
        requires ki < pow2_div(pow2(L), len).full
        requires ntt_indicies_inv(idxs, len, ki); 
        ensures poly_eval_all_points(a, y, len);
        ensures len.full == 2 ==> 
            idxs[0].bins == Reverse(orignal_index(ki, 0, len).bins);
        ensures len.full == 2 ==> 
            idxs[1].bins == Reverse(orignal_index(ki, 1, len).bins);
        decreases len.full
    {
        if len.full == 2 then 
            var len' := pow2_half(len);
            pow2_basics(len');

            var a_e := even_indexed_terms(a, len');
            var a_o := odd_indexed_terms(a, len');

            assert a_e[0] == poly_eval(a_e, omega_nk(len', 0)) by {
                assert a_e[0] == a[0];
                ntt_rec_base_case(a_e, len');
            }
            assert a_o[0] == poly_eval(a_o, omega_nk(len', 0)) by {
                assert a_o[0] == a[1];
                ntt_rec_base_case(a_o, len');
            }

            var y_ks := compute_y_k(a, a_e, a_o, a_e, a_o, len, 0);
            var y_k's := compute_y_k'(a, a_e, a_o, a_e, a_o, len, 0);

            ntt_indicies_inv_consequence(idxs, len, ki);
            [y_ks, y_k's]
        else
            var len' := pow2_half(len);
            var a_e := even_indexed_terms(a, len');
            var a_o := odd_indexed_terms(a, len');

            ghost var idx_e := even_indexed_indices(idxs, len);
            ghost var idx_o := odd_indexed_indices(idxs, len);

            even_indexed_indices_reorder(idxs, len, idx_e, ki);
            odd_indexed_indices_reorder(idxs, len, idx_o, ki);

            var y_e := ntt_rec2(a_e, len', idx_e, 2 * ki);
            var y_o := ntt_rec2(a_o, len', idx_o, 2 * ki + 1);

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
    function method A(): seq<elem>
        ensures |A()| == N == pow2(L).full;

    function method Ar(): seq<elem>
        ensures |Ar()| == N == pow2(L).full;
        ensures forall i | 0 <= i < N ::
            Ar()[i] == A()[build_rev_index(i).v];

    // function method {:fuel 1} build_level_chunks(len: pow2_t): (cs: seq<seq<elem>>)
    //     requires 1 <= len.exp <= L
    //     ensures |cs| == pow2_div(pow2(L), len).full;
    //     ensures forall i | 0 <= i < |cs| :: |cs[i]| == len.full
    //     decreases L - len.exp
    // {
    //     if len.exp == L then [A()]
    //     else 
    //         var a := build_level_chunks(pow2_double(len));
    //         assert |a| == pow2(L - len.exp - 1).full by {
    //             assert |a| == pow2(L).full / (pow2(len.exp + 1).full);
    //             reveal Pow2();
    //             assert len.exp + 1 <= L;
    //             LemmaPowSubtracts(2, len.exp + 1, L);
    //         }
    //         assert |a| * 2 == pow2(L - len.exp).full by {
    //             reveal Pow2();
    //             LemmaPowAdds(2, L - len.exp - 1, 1);
    //             LemmaPow1(2);
    //         }
    //         seq(|a| * 2, k requires 0 <= k < |a| * 2 => 
    //             if k % 2 == 0 then even_indexed_terms(a[k/2], len)
    //             else odd_indexed_terms(a[(k-1)/2], len))
    // }

    // function method get_level_chunk(len: pow2_t, ki: nat): (chunk: seq<elem>)
    //     requires 1 <= len.exp <= L
    //     requires ki < pow2_div(pow2(L), len).full;
    //     ensures |chunk| == len.full
    // {
    //     build_level_chunks(len)[ki]
    // }
}

