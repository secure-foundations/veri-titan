include "ntt_rec3.dfy"
include "index.dfy"

module ntt {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul

    import opened pows_of_2
    import opened omegas
    import opened ntt_rec
    import opened rindex

    import opened ntt_recs2
    import opened ntt_recs3


    type n_sized = s: seq<elem>
        | |s| == N == pow2(L).full witness *

    lemma chunk_index_bounded(len: pow2_t, ki: nat)
        requires 0 <= len.exp <= L;
        requires ki < chunk_count(len);
        ensures 0 <= ki * len.full <= N - len.full;
    {
        var max_count := chunk_count(len);
        var csize := len.full;
        nth_root_lemma();
        calc {
            ki * csize;
        <=  { LemmaMulUpperBound(ki, max_count - 1, csize, csize); }
            (max_count - 1) * csize;
            { LemmaMulIsCommutativeAuto(); }
            csize * (max_count - 1);
            { LemmaMulIsDistributiveSubAuto(); }
            max_count * csize - 1 * csize;
            N -  csize;
        }
        LemmaMulNonnegative(ki, csize);
    }

    lemma chunk_index_bounded_auto(len: pow2_t)
        requires 0 <= len.exp <= L;
        ensures forall ki | 0 <= ki < chunk_count(len) ::
            0 <= ki * len.full <= N - len.full;
    {
        forall ki |  0 <= ki < chunk_count(len)
            ensures 0 <= ki * len.full <= N - len.full;
        {
            chunk_index_bounded(len, ki);
        }
    }

    function read_chunk(y: n_sized, len: pow2_t, ki: nat): seq<elem>
        requires 0 <= len.exp <= L;
        requires ki < chunk_count(len);
        ensures 0 <= ki * len.full <= N - len.full;
    {
        chunk_index_bounded(len, ki);
        y[ki * len.full..ki * len.full + len.full]
    }

    function y_as_chunks(y: n_sized, len: pow2_t): (cs: seq<seq<elem>>)
        requires 0 <= len.exp <= L;
    {
        var max_count := chunk_count(len);
        seq(max_count, ki requires 0 <= ki < max_count => read_chunk(y, len, ki))
    }

    lemma y_as_chunks_index_lemma(y: n_sized, len: pow2_t, ki: nat)
        requires 0 <= len.exp <= L;
        requires ki < chunk_count(len);
        ensures y_as_chunks(y, len)[ki] == read_chunk(y, len, ki);
    {
    }

    datatype ntt_loop_lvls = ntt_loop_lvls(
        lower: level_view,
        higher: level_view)
    {
        predicate ntt_loop_views_wf()
        {
            && N == pow2(L).full
            && 2 <= higher.m.full <= N
            && 1 <= higher.m.exp <= L
            && lower.m == pow2_half(higher.m)
            && lower.valid_level_view()
            && higher.valid_level_view()
        }

        function lo_idx(ki: nat): (i: nat)
            requires ntt_loop_views_wf();
            requires ki <= chunk_count(higher.m)
            ensures i <= chunk_count(lower.m);
        {
            chunk_count_half(higher.m);
            ki * 2
        }

        function hi_idx(ki: nat): nat
            requires ntt_loop_views_wf();
            requires ki <= chunk_count(higher.m);
        {
            ki
        }

        lemma hi_lo_idx_relations(ki: nat)
            requires ntt_loop_views_wf();
            requires ki <= chunk_count(higher.m);
            ensures  0 <= lo_idx(ki) * lower.m.full == hi_idx(ki) * higher.m.full;
            ensures hi_idx(ki) < chunk_count(higher.m) ==> 
                lo_idx(ki) < chunk_count(lower.m) - 1;
        {
            calc == {
                hi_idx(ki) * higher.m.full;
                {
                    LemmaMulIsAssociativeAuto();
                }
                ki * 2 * lower.m.full;
                {
                    LemmaMulIsAssociativeAuto();
                }
                lo_idx(ki) * lower.m.full;
            }

            if hi_idx(ki) < chunk_count(higher.m) {
                chunk_count_half(higher.m);
                assert chunk_count(higher.m) * 2 == chunk_count(lower.m);
                assert ki <= chunk_count(higher.m) - 1;
                assert ki * 2 <= (chunk_count(higher.m) - 1) * 2;
                assert lo_idx(ki) < chunk_count(lower.m) - 1;
            }

            LemmaMulNonnegative(lo_idx(ki), lower.m.full);
        }

        lemma index_bounded_lemma(ki: nat, j: nat)
            requires ntt_loop_views_wf();
            requires ki <= chunk_count(higher.m);
            requires 0 <= j <= lower.m.full;
            requires ki < chunk_count(higher.m);
            ensures j != lower.m.full ==>
                0 <= ki * higher.m.full + j + lower.m.full < N;
            ensures j == lower.m.full ==>
                0 <= ki * higher.m.full + j + lower.m.full <= N;
        {
            var len := higher.m.full;
            chunk_index_bounded(higher.m, ki);
            assert 0 <= ki * len <= N - len;
        }

        predicate ntt_level_loop_inv(y: n_sized, ki: nat)
        {
            && ntt_loop_views_wf()
            && ki <= chunk_count(higher.m)
            && |y| == N == pow2(L).full
            && y_as_chunks(y, lower.m)[lo_idx(ki)..]
                == lower.ntt_rec3()[lo_idx(ki)..]
            // && y_as_chunks(y, higher.m)[..hi_idx(ki)]
            //     == higher_prefix()
        }

        function start_point(ki: nat): (k: nat)
            requires ntt_loop_views_wf();
            requires ki < chunk_count(higher.m);
            ensures k == hi_idx(ki) * higher.m.full;
            ensures 0 <= k <= N - higher.m.full;
        {
            hi_lo_idx_relations(ki);
            chunk_index_bounded(higher.m, ki);
            lo_idx(ki) * lower.m.full
        }

        function split_point(ki: nat): (k: nat)
            requires ntt_loop_views_wf();
            requires ki < chunk_count(higher.m);
            ensures 0 <= k <= N - lower.m.full;
        {
            start_point(ki) + lower.m.full
        }

        function end_point(ki: nat): (k: nat)
            requires ntt_loop_views_wf();
            requires ki < chunk_count(higher.m);
            ensures 0 <= k <= N;
        {
            start_point(ki) + higher.m.full
        }

        function read_even_chunk(y: n_sized, ki: nat): (c: seq<elem>)
            requires ntt_level_loop_inv(y, ki);
            requires ki < chunk_count(higher.m);
            ensures c == y[start_point(ki)..split_point(ki)];
        {
            hi_lo_idx_relations(ki);
            read_chunk(y, lower.m, lo_idx(ki))
        }

        function read_odd_chunk(y: n_sized, ki: nat): (c: seq<elem>)
            requires ntt_level_loop_inv(y, ki);
            requires ki < chunk_count(higher.m);
            ensures c == y[split_point(ki)..end_point(ki)];
        {
            chunk_index_bounded(higher.m, ki);
            hi_lo_idx_relations(ki);
            assert y[split_point(ki)..end_point(ki)]
                == read_chunk(y, lower.m, lo_idx(ki)+1)
            by {
                var csize := lower.m.full;
                var kl := lo_idx(ki);
                calc == {
                    y[split_point(ki)..end_point(ki)];
                    y[kl*csize+csize..kl*csize+2*csize];
                    {
                        LemmaMulIsDistributiveAddOtherWayAuto();
                    }
                    y[(kl+1) * csize..kl*csize+csize+csize];
                    {
                        LemmaMulIsDistributiveAddOtherWayAuto();
                    }
                    y[(kl+1) * csize..(kl+1) * csize+csize];
                    read_chunk(y, lower.m, kl + 1);
                }
            }
            read_chunk(y, lower.m, lo_idx(ki)+1)
        }

        lemma lower_view_correspondence(y: n_sized, ki: nat)
            requires ntt_level_loop_inv(y, ki);
            requires ki < chunk_count(higher.m);
            ensures lo_idx(ki) < |lower.a| - 1;
            ensures poly_eval_all_points(lower.a[lo_idx(ki)], read_even_chunk(y, ki), lower.m);
            ensures poly_eval_all_points(lower.a[lo_idx(ki)+1], read_odd_chunk(y, ki), lower.m);
        {
            var k := start_point(ki);
            var len' := lower.m;
            var csize := len'.full;
            index_bounded_lemma(ki, csize);
            var even_chunk := y[k..k+csize];
            var odd_chunk := y[k+csize..k+csize*2];
            var gy := y_as_chunks(y, lower.m);
            var vy := lower.ntt_rec3();

            var kl := lo_idx(ki);
            assert gy[kl..] == vy[kl..];

            hi_lo_idx_relations(ki);
            assert k == kl * csize;
            calc == {
                odd_chunk;
                y[kl*csize+csize..kl*csize+2*csize];
                {
                    LemmaMulIsDistributiveAddOtherWayAuto();
                }
                y[(kl+1) * csize..kl*csize+csize+csize];
                {
                    LemmaMulIsDistributiveAddOtherWayAuto();
                }
                y[(kl+1) * csize..(kl+1) * csize+csize];
                read_chunk(y, len', kl + 1);
            }
            assert even_chunk == read_chunk(y, len', kl);
            assert odd_chunk == read_chunk(y, len', kl + 1);

            assert even_chunk == vy[kl];
            assert odd_chunk == vy[kl + 1];
        }

        predicate ntt_chunk_loop_inv(y: n_sized, y': n_sized,
            omg: elem, ki: nat, j: nat)
        {
            && ntt_level_loop_inv(y, ki)
            && j <= lower.m.full
            && omg == omega_nk(higher.m, j)
            && ki < chunk_count(higher.m)
            && var a := start_point(ki);
            && var b := split_point(ki);
            && var c := end_point(ki);
            && |y'| == |y|
            && y'[..a] == y[..a]
            && y'[a+j..b] == y[a+j..b] == read_even_chunk(y, ki)[j..]
            && y'[a..a+j] == 
            && y'[b+j..c] == y[b+j..c] == read_odd_chunk(y, ki)[j..]
            && y'[b..b+j] == 
            && y'[c..] == y[c..]
        }

        lemma chunk_loop_pre_lemma(y: n_sized, ki: nat)
            requires ntt_level_loop_inv(y, ki);
            requires ki < chunk_count(higher.m);
            ensures ntt_chunk_loop_inv(y, y, 1, ki, 0);
        {
            var a := start_point(ki);
            var b := split_point(ki);
            var c := end_point(ki);

            assert y[a..b] == read_even_chunk(y, ki);
            assert y[b..c] == read_odd_chunk(y, ki);

            assert 1 == omega_nk(higher.m, 0) by {
                LemmaPow0Auto();
            }
        }

        // lemma chunk_loop_peri_lemma(y: n_sized,
        //     y1: n_sized, y2: n_sized,
        //     omg: elem, t: elem, u: elem,
        //     ki: nat, j: nat)
        //     requires ntt_chunk_loop_inv(y, y1, omg, ki, j);
        //     requires j < lower.m.full;
        //     requires t == modmul(omg, y[split_point(ki) + j]);
        //     requires u == y[start_point(ki) + j];
        //     requires y2 == y1[start_point(ki) + j := modadd(u, t)]
        //         [split_point(ki) + j := modsub(u, t)];
        // {
        //     var a := start_point(ki);
        //     var b := split_point(ki);
        //     var c := end_point(ki);

        //     calc == {
        //         y2[a+j+1..b];
        //         y1[a+j+1..b];
        //         y[a+j+1..b];
        //         read_even_chunk(y, ki)[j+1..];
        //     }

        //     calc == {
        //         y2[b+j+1..c];
        //         y1[b+j+1..c];
        //         y[b+j+1..c];
        //         read_odd_chunk(y, ki)[j+1..];
        //     }

        //     omg_inv(omgm, omg, higher.m, j);
        // }
    }

    method ntt_chunk_loop(
        y: n_sized, 
        k: nat,
        ki: nat,
        view: ntt_loop_lvls)
    returns (y': seq<elem>)
        requires view.ntt_level_loop_inv(y, ki);
        requires ki < chunk_count(view.higher.m);
        requires k == view.hi_idx(ki) * view.higher.m.full;
    {
        y' := y;
        var len' := view.lower.m;
        var omgm := omega_n(view.higher.m);

        var omg := 1;
        var j := 0;

        pow2_basics(view.higher.m);

        view.index_bounded_lemma(ki, 0);
        view.chunk_loop_pre_lemma(y, ki);

        while (j < len'.full)
            invariant view.ntt_chunk_loop_inv(y, y', omg, ki, j);
        {
            var y1 := y;
            view.index_bounded_lemma(ki, j);

            var t := modmul(omg, y[k + j + len'.full]);
            var u := y[k + j];
            y' := y'[k + j := modadd(u, t)];
            y' := y'[k + j + len'.full := modsub(u, t)];

            view.chunk_loop_peri_lemma(y, y1, y', omg, t, u, ki, j);

            omg := modmul(omg, omgm);
            j := j + 1;
            assume false;
        }

        // assert y[..k] == y'[..k];
        // assert y[k+m.full..] == y'[k+m.full..];
    }


    // method ntt_level_loop(a: seq<elem>, s: nat)
    //     requires |a| == N == pow2(L).full;
    //     requires 1 <= s < L;
    // {
    //     var m := pow2(s);
    //     pow2_basics(m);
    //     assume 1 <= m.full <= N/2;

    //     var omgm := omega_nk(m, 1);

    //     assert omega_nk(m, 1) == omega_n(m) by {
    //         LemmaPow1Auto();
    //     }

    //     var k := 0;
    //     var ki := 0;

    //     while (ki < pow2_div(pow2(L), m).full) 
    //         // at level s, each chunk is 2 ** s big
    //         // invariant step_count == pow2_div(pow2(L), m);
    //         // invariant step_count.exp == L - m.exp;
    //         invariant 0 <= k == ki * m.full;
    //     {
    //         var k' := k + m.full;
    //         var ki' := ki + 1;

    //         var _ := ntt_chunk_loop(a, k, ki, m);

    //         assert k' == (ki + 1) * m.full by {
    //             LemmaMulIsDistributiveAddOtherWay(m.full, ki, 1);
    //             assert (ki + 1) * m.full == ki * m.full + 1 * m.full;
    //         }
    //         assert (ki + 1) * m.full > 0 by {
    //             LemmaMulStrictlyPositiveAuto();
    //         }
    //         k, ki := k', ki';
    //     }
    // }

    // method ntt(b: seq<elem>, len: pow2_t) returns (y: n_sized)
    //     requires |b | == len.full == N;
    //     requires len.exp == L;
    //     // ensures poly_eval_all_points(a, y, len)
    // {
    //     // var s := pow2(0);
    //     var s := 1;
    //     while (s < L) // L levels totoal, combine results at each level 
    //         invariant 1 <= s;
    //     {
    //         ntt_level_loop(b, s);
    //         s := s + 1;
    //     }
    // }


      // lemma init_implies_inv(
    //     y: n_sized,
    //     m: pow2_t, 
    //     a: seq<seq<elem>>,
    //     idxs: seq<seq<index_t>>)

    //     requires |y| == N == pow2(L).full
    //     requires 1 == m.full;
    //     requires 0 == m.exp;
    //     requires ntt_chunk_indicies_inv(a, idxs, m);
    //     requires y == Ar();
    //     ensures ntt_level_loop_inv(y, m, a, idxs);
    // {
    //     var view := y_as_chunks(y, m);
    //     var base := ntt_rec3_base(a, m, idxs);
    //     forall ki | 0 <= ki < N
    //         ensures view[ki] == base[ki];
    //     {
    //         calc == {
    //             view[ki];
    //             y[ki..ki+1];
    //             [y[ki]];
    //             [Ar()[ki]];
    //             base[ki];
    //         }
    //     }
    // }
}




    // function {:opaque} y_as_chunks_prefix(y: n_sized, len: pow2_t, i: nat): seq<seq<elem>>
    //     requires 0 <= len.exp <= L;
    //     requires i <= chunk_count(len);
    // {
    //     var count := i;
    //     var csize := len.full;
    //     chunk_index_bounded_auto(len);
    //     seq(count, ki requires 0 <= ki < count => y[ki * csize..ki * csize + csize])    
    // }

    // lemma y_as_chunks_prefix_lemma(y: n_sized, y': n_sized, len: pow2_t, i: nat)
    //     requires 0 <= len.exp <= L;
    //     requires i <= chunk_count(len);
    //     requires 0 <= i * len.full <= N;
    //     requires y[..i * len.full] == y'[..i * len.full];
    //     ensures y_as_chunks_prefix(y, len, i) == y_as_chunks_prefix(y', len, i);
    // {
    //     reveal y_as_chunks_prefix();
    //     var csize := len.full;
    //     var v1 := y_as_chunks_prefix(y, len, i);
    //     var v2 := y_as_chunks_prefix(y', len, i);

    //     forall ki: nat | 0 <= ki < i
    //         ensures v1[ki] == v2[ki];
    //     {
    //         chunk_index_bounded(len, ki);

    //         var lo := ki * csize;
    //         var hi := ki * csize + csize;

    //         assert hi <= i * len.full by {
    //             LemmaMulInequality(ki, i-1, len.full);
    //             LemmaMulIsCommutativeAuto();
    //             LemmaMulIsDistributiveSubAuto();
    //         }

    //         assert y[..hi] == y'[..hi];
    //         assert y[lo..hi] == y'[lo..hi];

    //     }
    // }

    // function {:opaque} y_as_chunks_suffix(y: n_sized, len: pow2_t, i: nat): seq<seq<elem>>
    //     requires 0 <= len.exp <= L;
    //     requires i <= chunk_count(len);
    // {
    //     var count := chunk_count(len) - i;
    //     var csize := len.full;
        
    //     assert forall ki | 0 <= ki < count ::
    //         0 <= (ki + i) * csize <= N - csize by {
    //         forall ki | 0 <= ki < count 
    //             ensures 0 <= (ki + i) * csize <= N - csize;
    //         {
    //             chunk_index_bounded(len, ki + i);
    //         }
    //     }
    //     seq(count, ki requires 0 <= ki < count => y[(ki + i) * csize..(ki + i) * csize + csize]) 
    // }

    // lemma y_as_chunks_suffix_lemma(y: n_sized, y': n_sized, len: pow2_t, i: nat)
    //     requires 0 <= len.exp <= L;
    //     requires i <= chunk_count(len);
    //     requires 0 <= i * len.full <= N;
    //     requires y[i * len.full..] == y'[i * len.full..];
    //     ensures y_as_chunks_suffix(y, len, i) == y_as_chunks_suffix(y', len, i);
    // {
    //     reveal y_as_chunks_suffix();
    //     var count := chunk_count(len) - i;
    //     var csize := len.full;
    //     var v1 := y_as_chunks_suffix(y, len, i);
    //     var v2 := y_as_chunks_suffix(y', len, i);

    //     forall ki: nat | 0 <= ki < count
    //         ensures v1[ki] == v2[ki];
    //     {
    //         chunk_index_bounded(len, ki + i);

    //         var lo := (ki + i) * csize;
    //         var hi := lo + csize;

    //         assert i * len.full <= lo by {
    //             assert i <= ki + i;
    //             LemmaMulInequality(i, i+ki, len.full);
    //         }

    //         assert y[lo..] == y'[lo..];
    //         assert y[lo..hi] == y'[lo..hi];
    //     }
    // }