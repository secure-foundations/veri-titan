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

    lemma index_bounded_lemma(
        j: nat, k: nat, ki: nat,
        m: pow2_t)
        requires m.full >= 2;
        requires 0 <= j < m.full / 2;
        requires N == pow2(L).full;
        requires 1 <= m.exp <= L;
        requires k == ki * m.full;
        requires ki < pow2_div(pow2(L), m).full;
        ensures k + j + m.full / 2 < N;
    {
        pow2_basics(m);
        var half_step := m.full / 2;

        calc {
            k + j + m.full / 2;
        ==
            ki * m.full + j + half_step;
        <
            ki * m.full + 2 * half_step;
        ==
            ki * m.full + m.full;
        == { LemmaMulIsDistributiveAddOtherWay(m.full, ki, 1); }
            (ki + 1) * m.full;
        <= { assert ki + 1 <= pow2_div(pow2(L), m).full; LemmaMulInequalityAuto(); }
            pow2_div(pow2(L), m).full * m.full;
        ==
            N;
        }
    }

    type n_sized = s: seq<elem>
        | |s| == N == pow2(L).full witness *

    function method chunk_count(len: pow2_t): pow2_t
        requires 0 <= len.exp <= L;
    {
        pow2_div(pow2(L), len)
    }

    lemma chunk_index_bounded(len: pow2_t, ki: nat)
        requires 0 <= len.exp <= L;
        requires ki < chunk_count(len).full;
        ensures 0 <= ki * len.full <= N - len.full;
    {
        var max_count := pow2_div(pow2(L), len).full;
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
        ensures forall ki | 0 <= ki < chunk_count(len).full ::
            0 <= ki * len.full <= N - len.full;
    {
        forall ki |  0 <= ki < chunk_count(len).full 
            ensures 0 <= ki * len.full <= N - len.full;
        {
            chunk_index_bounded(len, ki);
        }
    }

    predicate n_sized_diff_chunk(y: n_sized, y': n_sized, len: pow2_t, ki: nat)
        requires 0 <= len.exp <= L;
        requires ki < chunk_count(len).full;
    {
        var offset := ki * len.full;
        chunk_index_bounded(len, ki);
        forall i | (0 <= i < offset || offset + len.full <= i < N) :: 
            y'[i] == y[i] 
    }

    function view_as_chunks(y: n_sized, len: pow2_t): seq<seq<elem>>
        requires 0 <= len.exp <= L;
    {
        var max_count := pow2_div(pow2(L), len).full;
        var csize := len.full;
        chunk_index_bounded_auto(len);
        seq(max_count, ki requires 0 <= ki < max_count => y[ki * csize..ki * csize + csize])
    }

    function view_as_chunks_prefix(y: n_sized, len: pow2_t, i: nat): seq<seq<elem>>
        requires 0 <= len.exp <= L;
        requires i <= pow2_div(pow2(L), len).full;
    {
        var max_count := pow2_div(pow2(L), len).full;
        var count := i;
        var csize := len.full;
        chunk_index_bounded_auto(len);
        seq(count, ki requires 0 <= ki < count => y[ki * csize..ki * csize + csize])    
    }

    function view_as_chunks_suffix(y: n_sized, len: pow2_t, i: nat): seq<seq<elem>>
        requires 0 <= len.exp <= L;
        requires i <= pow2_div(pow2(L), len).full;
    {
        var max_count := pow2_div(pow2(L), len).full;
        var count := max_count - i;
        var csize := len.full;
        chunk_index_bounded_auto(len);
        seq(count, ki requires 0 <= ki < count => y[ki * csize..ki * csize + csize]) 
    }

    // lemma chunks_view_update(y: n_sized, y': n_sized,
    //     len1: pow2_t, view1: seq<seq<elem>>,
    //     len2: pow2_t, view2: seq<seq<elem>>,
    //     ki: nat)
    //     requires ki < |view2|;
    //     requires 1 <= len2.exp <= L;
    //     requires len1 == pow2_half(len2);
    //     requires view_as_chunks(y, len1) == view1;
    //     requires view_as_chunks(y, len2) == view2;
    //     requires forall i | 0 <= i < ki * len2.full < N :: y'[i] == y[i];
    //     requires forall i | 0 <= ki * len2.full <= i < N :: y'[i] == y[i];
    // {

    // }

    // predicate ntt_chunk_loop_inv(
    //     y: seq<elem>,
    //     m: pow2_t, 
    //     a: seq<seq<elem>>,
    //     idxs: seq<seq<index_t>>,
    //     ki: nat)
    //     requires |y| == N == pow2(L).full
    //     requires 1 <= m.full;
    //     requires 0 <= m.exp <= L;
    //     requires ki < pow2_div(pow2(L), m).full;
    //     requires ntt_chunk_indicies_inv(a, idxs, m);
    // {
    //     view_as_chunks(y, m)[..ki] == ntt_rec3(a, m, idxs)[..ki]
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

    // method ntt_chunk_loop(
    //     y: seq<elem>,
    //     k: nat,
    //     m: pow2_t,
    //     ghost ki: nat,
    //     ghost a: seq<seq<elem>>,
    //     ghost idxs: seq<seq<index_t>>)

    // returns (y': seq<elem>)
    //     requires 1 <= m.exp <= L;
    //     requires ntt_chunk_indicies_inv(a, idxs, pow2_half(m));
    //     requires |y| == N == pow2(L).full;
    //     requires ki < pow2_div(pow2(L), m).full;
    //     requires k == ki * m.full;
    //     requires ntt_chunk_loop_inv(y, pow2_half(m), a, idxs, ki);
    // {
    //     y' := y;
    //     var len' := pow2_half(m);
    //     var omgm := omega_n(m);

    //     var omg := 1;
    //     var j := 0;

    //     assert omg == modpow(omgm, 0) by {
    //         LemmaPow0Auto();
    //     }

    //     pow2_basics(m);

    //     index_bounded_lemma(0, k, ki, m);

    //     // ghost var y_o := y[k..k+len'.full];
    //     // ghost var y_e := y[k+len'.full..k+m.full];
    //     // ghost var y_ks := compute_y_ks(a[ki], y_e, y_o, m);

    //     while (j < len'.full)
    //         invariant 0 <= j <= len'.full;
    //         invariant omg == modpow(omgm, j);
    //         invariant |y'| == |y|;
    //         invariant k + j + len'.full <= N;
    //         invariant y[..k] == y'[..k];
    //         invariant y[k+j..k+len'.full] == y'[k+j..k+len'.full];
    //         invariant y[k+len'.full+j..] == y'[k+len'.full+j..];
    //     {
    //         index_bounded_lemma(j, k, ki, m);
    //         var t := modmul(omg, y[k + j + len'.full]);
    //         var u := y[k + j];
    //         y' := y'[k + j := modadd(u, t)];
    //         y' := y'[k + j + len'.full := modsub(u, t)];

    //         omg_inv(omgm, omg, m, j);
    //         omg := modmul(omg, omgm);
    //         j := j + 1;

    //         // if m.exp == 1 {
    //         //    ghost var y_exp := ntt_rec2_base(a[ki], m, idxs[ki], ki);
    //         //    assert y'[k..k+2] == y_exp; 
    //         // }
    //     }

    //     // assert y[..k] == y'[..k];
    //     // assert y[k+m.full..] == y'[k+m.full..];
    // }

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
}

