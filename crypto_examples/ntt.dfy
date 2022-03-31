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

    predicate n_sized_diff_chunk(y1: n_sized, y2: n_sized, len: pow2_t, ki: nat)
        requires 0 <= len.exp <= L;
        requires ki < chunk_count(len);
    {
        var offset := ki * len.full;
        chunk_index_bounded(len, ki);
        forall i | (0 <= i < offset || offset + len.full <= i < N) :: 
            y1[i] == y2[i]
    }

    function view_as_chunks(y: n_sized, len: pow2_t): seq<seq<elem>>
        requires 0 <= len.exp <= L;
    {
        var max_count := chunk_count(len);
        var csize := len.full;
        chunk_index_bounded_auto(len);
        seq(max_count, ki requires 0 <= ki < max_count => y[ki * csize..ki * csize + csize])
    }

    lemma n_sized_diff_chunk_view(y1: n_sized, y2: n_sized, len: pow2_t, ki: nat)
        requires 0 <= len.exp <= L;
        requires ki < chunk_count(len);
        requires n_sized_diff_chunk(y1, y2, len, ki);
        ensures view_as_chunks(y2, len) ==
            view_as_chunks(y1, len)[ki := view_as_chunks(y2, len)[ki]]
    {
        var v1 := view_as_chunks(y1, len);
        var v2 := view_as_chunks(y2, len);
        chunk_index_bounded_auto(len);
        var csize := len.full;

        forall i | 0 <= i < chunk_count(len)
            ensures i != ki ==> v1[i] == v2[i];
        {
            if i != ki {
                var lo := i * csize;
                var hi := i * csize + csize;
                assume y1[lo..hi] == y2[lo..hi]; // TODO
                assert v1[i] == v2[i];
            }
        }
        assert v2 == v1[ki := v2[ki]];
    }

    function {:opaque} view_as_chunks_prefix(y: n_sized, len: pow2_t, i: nat): seq<seq<elem>>
        requires 0 <= len.exp <= L;
        requires i <= chunk_count(len);
    {
        var max_count := chunk_count(len);
        var count := i;
        var csize := len.full;
        chunk_index_bounded_auto(len);
        seq(count, ki requires 0 <= ki < count => y[ki * csize..ki * csize + csize])    
    }

    function {:opaque} view_as_chunks_suffix(y: n_sized, len: pow2_t, i: nat): seq<seq<elem>>
        requires 0 <= len.exp <= L;
        requires i <= chunk_count(len);
    {
        var max_count := chunk_count(len);
        var count := max_count - i;
        var csize := len.full;
        chunk_index_bounded_auto(len);
        seq(count, ki requires 0 <= ki < count => y[ki * csize..ki * csize + csize]) 
    }

    datatype ntt_loop_lvls = ntt_loop_lvls(
        lower: level_view,
        higher: level_view,
        ki: nat)
    {
        predicate ntt_loop_views_wf()
        {
            && N == pow2(L).full
            && 2 <= higher.m.full <= N
            && 1 <= higher.m.exp <= L
            && lower.m == pow2_half(higher.m)
            && ki <= chunk_count(higher.m)
            && lower.valid_level_view()
            && higher.valid_level_view()
        }

        function lower_idx(): (i: nat)
            requires ntt_loop_views_wf();
            ensures i <= chunk_count(lower.m);
        {
            chunk_count_half(higher.m);
            ki * 2
        }

        function higher_idx(): nat
        {
            ki
        }

        function lower_suffix(): seq<seq<elem>>
            requires ntt_loop_views_wf()
        {
            lower.ntt_rec3()[..lower_idx()]
        }

        function higher_prefix(): seq<seq<elem>>
            requires ntt_loop_views_wf()
        {
            higher.ntt_rec3()[higher_idx()..]
        }

        lemma index_bounded_lemma(
            j: nat)
            requires ntt_loop_views_wf();
            requires 0 <= j < lower.m.full;
            requires ki < chunk_count(higher.m);
            ensures 0 <= ki * higher.m.full + j + lower.m.full < N;
        {
            var len := higher.m.full;
            chunk_index_bounded(higher.m, ki);
            assert 0 <= ki * len <= N - len;
        }
    }
    
    predicate ntt_chunk_loop_inv(
        y: seq<elem>,
        view: ntt_loop_lvls)
    {
        && view.ntt_loop_views_wf()
        && |y| == N == pow2(L).full
        && view_as_chunks_suffix(y, view.lower.m, view.lower_idx())
            == view.lower_suffix()
        && view_as_chunks_prefix(y, view.higher.m, view.higher_idx())
            == view.higher_prefix()
    }

    method ntt_chunk_loop(
        y: seq<elem>, 
        k: nat,
        view: ntt_loop_lvls)
    returns (y': seq<elem>)
        requires ntt_chunk_loop_inv(y, view);
        requires view.ki < chunk_count(view.higher.m);
        requires k == view.higher_idx() * view.higher.m.full;
    {
        y' := y;
        var len' := view.lower.m;
        var omgm := omega_n(view.higher.m);

        var omg := 1;
        var j := 0;

        assert omg == modpow(omgm, 0) by {
            LemmaPow0Auto();
        }

        pow2_basics(view.higher.m);

        view.index_bounded_lemma(0);

        while (j < len'.full)
            invariant 0 <= j <= len'.full;
            invariant omg == modpow(omgm, j);
            invariant |y'| == |y|;
            invariant k + j + len'.full <= N;
            invariant y[..k] == y'[..k];
            invariant y[k+j..k+len'.full] == y'[k+j..k+len'.full];
            invariant y[k+len'.full+j..] == y'[k+len'.full+j..];
        {
            view.index_bounded_lemma(j);

            var t := modmul(omg, y[k + j + len'.full]);
            var u := y[k + j];
            y' := y'[k + j := modadd(u, t)];
            y' := y'[k + j + len'.full := modsub(u, t)];

            omg_inv(omgm, omg, view.higher.m, j);
            omg := modmul(omg, omgm);
            j := j + 1;

            // if m.exp == 1 {
            //    ghost var y_exp := ntt_rec2_base(a[ki], m, idxs[ki], ki);
            //    assert y'[k..k+2] == y_exp; 
            // }
        }

    // //     // assert y[..k] == y'[..k];
    // //     // assert y[k+m.full..] == y'[k+m.full..];
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

    // method ntt(b: seq<elem>, len: pow2_t) returns (y: seq<elem>)
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
    //     y: seq<elem>,
    //     m: pow2_t, 
    //     a: seq<seq<elem>>,
    //     idxs: seq<seq<index_t>>)

    //     requires |y| == N == pow2(L).full
    //     requires 1 == m.full;
    //     requires 0 == m.exp;
    //     requires ntt_chunk_indicies_inv(a, idxs, m);
    //     requires y == Ar();
    //     ensures ntt_chunk_loop_inv(y, m, a, idxs);
    // {
    //     var view := view_as_chunks(y, m);
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

