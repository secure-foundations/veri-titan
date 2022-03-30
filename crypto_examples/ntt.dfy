include "ntt_rec2.dfy"
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

    // lemma ntt_chunk_base_case(a': seq<elem>, 
    //     k: nat, ki: nat, t: elem, u: elem,
    //     m: pow2_t)

    //     requires |a'| == N == pow2(L).full;
    //     requires m.exp == 1;
    //     requires ki < pow2_div(pow2(L), m).full;
    //     requires k == ki * m.full;
    //     requires k < k + 1 < N;

    //     requires t == modmul(1, Ar()[k + 1]);
    //     requires u == Ar()[k];
    //     requires a'[k] == modadd(u, t);
    //     requires a'[k+1] == modsub(u, t);

    //     ensures Ar()[k..k+2] == get_level_chunk(m, ki);
    //     ensures a'[k] == poly_eval(get_level_chunk(m, ki), omega_nk(m, 0));
    //     ensures a'[k+1] == poly_eval(get_level_chunk(m, ki), omega_nk(m, 1));
    // {
    //     pow2_basics(m);
    //     var m' := pow2_half(m);

    //     assert t == Ar()[k + 1] by {
    //         assert Ar()[k + 1] < Q;
    //     }

    //     var even := Ar()[k..k+1];
    //     var odd := Ar()[k+1..k+2];
    //     var chunk :=Ar()[k..k+2];
    //     assert chunk == even + odd;

    //     var original := orignal_index(ki, 0, m);
    //     assert original.v == k;

    //     ntt_rec_base_case(odd, m');
    //     ntt_rec_base_case(even, m');

    //     assert u == poly_eval(even, omega_nk(m', 0));
    //     assert t == poly_eval(odd, omega_nk(m', 0));

    //     var omg := omega_nk(m, 0);

    //     calc == {
    //         modmul(omg, t);
    //         {
    //             LemmaPow0(omega_n(m));
    //         }
    //         modmul(1, t);
    //     }

    //     y_k_value(chunk, even, odd, pow2(0), pow2(1),
    //         omg, 0, u, t, a'[k]);

    //     y_k'_value(chunk, even, odd, pow2(0), pow2(1),
    //         omg, 0, u, t, a'[k+1]);

    //     // assert |get_level_chunk(m, ki)| == 2;
    //     assume Ar()[k..k+2] == get_level_chunk(m, ki);
    // }

    // function view_as_chunks(y: seq<elem>, len: pow2_t): seq<seq<elem>>
    //     requires |y| == N == pow2(L).full
    //     requires 1 <= len.exp <= L
    // {
    //     var count := pow2_div(pow2(L), len).full;
    //     var csize := len.full;
    //     assert forall ki |  0 <= ki < count :: 0 <= ki * csize <= N - csize by {
    //         forall ki |  0 <= ki < count 
    //             ensures 0 <= ki * csize <= N - csize
    //         {
    //             nth_root_lemma();
    //             calc {
    //                 ki * csize;
    //             <=  { LemmaMulUpperBound(ki, count - 1, csize, csize); }
    //                 (count - 1) * csize;
    //                 { LemmaMulIsCommutativeAuto(); }
    //                 csize * (count - 1);
    //                 { LemmaMulIsDistributiveSubAuto(); }
    //                 count * csize - 1 * csize;
    //                 N -  csize;
    //             }
    //             LemmaMulNonnegative(ki, csize);
    //         }
    //     }
    //     seq(count, ki requires 0 <= ki < count => y[ki * csize..ki * csize + csize])
    // }

    // predicate ntt_chunk_loop_inv(
    //     y: seq<elem>,
    //     m: pow2_t,
    //     ki: nat,
    //     a: seq<seq<elem>>,
    //     idxs: seq<seq<index_t>>)
    //     requires ntt_chunk_indicies_inv(a, idxs, m);
    // {
    //     view_as_chunks(y, m)[ki] == ntt_rec2(a[ki], m, idxs[ki], ki)
    // }

    method ntt_chunk_loop(
        y: seq<elem>,
        k: nat,
        m: pow2_t,
        ghost ki: nat,
        ghost a: seq<seq<elem>>,
        ghost idxs: seq<seq<index_t>>)

    returns (y': seq<elem>)
        requires ntt_chunk_indicies_inv(a, idxs, m);
        // this loop works on a chunk of size m.full
        // by combining two smaller chunks of size m.full/2
        // m.full: the chunk size at the current level
        requires |y| == N == pow2(L).full;
        // m.exp: the level, go from 1 to L (log N)
        // ki: the chunk id at current level, go from 0 to N/m
        requires ki < pow2_div(pow2(L), m).full;
        // k is ki times chunk size, points to start of the chunk
        requires k == ki * m.full;
        requires m.exp == 1 ==> y == Ar();
    {
        y' := y;
        var len' := pow2_half(m);
        var omgm := omega_n(m);

        var omg := 1;
        var j := 0;

        assert omg == modpow(omgm, 0) by {
            LemmaPow0Auto();
        }

        pow2_basics(m);

        index_bounded_lemma(0, k, ki, m);

        // ghost var y_o := y[k..k+len'.full];
        // ghost var y_e := y[k+len'.full..k+m.full];
        // ghost var y_ks := compute_y_ks(a[ki], y_e, y_o, m);

        while (j < len'.full)
            invariant 0 <= j <= len'.full;
            invariant omg == modpow(omgm, j);
            invariant |y'| == |y|;
            invariant k + j + len'.full <= N;
            invariant y[..k] == y'[..k];
            invariant y[k+j..k+len'.full] == y'[k+j..k+len'.full];
            invariant y[k+len'.full+j..] == y'[k+len'.full+j..];
        {
            index_bounded_lemma(j, k, ki, m);
            var t := modmul(omg, y[k + j + len'.full]);
            var u := y[k + j];
            y' := y'[k + j := modadd(u, t)];
            y' := y'[k + j + len'.full := modsub(u, t)];

            omg_inv(omgm, omg, m, j);
            omg := modmul(omg, omgm);
            j := j + 1;

            // if m.exp == 1 {
            //    ghost var y_exp := ntt_rec2_base(a[ki], m, idxs[ki], ki);
            //    assert y'[k..k+2] == y_exp; 
            // }
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

