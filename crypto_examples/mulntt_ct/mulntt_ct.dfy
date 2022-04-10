include "nth_root.dfy"

module ntt {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul

    import opened pows_of_2
    import opened omegas
    // import opened ntt_recs
    // import opened rindex
    // import opened bins
    // import opened polys

    type n_sized = s: seq<elem>
        | |s| == N == pow2(LOGN).full witness *

    function method A(): seq<elem>
        ensures |A()| == N == pow2(LOGN).full;

    function method P(): seq<elem>
        ensures |P()| == N == pow2(LOGN).full;

    method slice_loop(u: nat,
        d: pow2_t,
        w: elem,
        ghost j: nat,
        ghost blocks: seq<seq<elem>>)
        requires |blocks| == d.full;
    {
        var s := u;

        while (s < u + d.full)
        {
            ghost var b_idx := s - u;

            var oi := s + d.full;
            var ei := s;

            s := s + 1;

            // blocks[b_idx := blocks[b_idx]];
        }
    }

    lemma P_table_index_bounded(t: pow2_t, j: nat)
        requires t.exp < LOGN;
        requires j < t.full;
        ensures t.full + j < N;
    {
        assume false;
    }

    method level_loop(t: pow2_t, d: pow2_t)
        requires t.exp < LOGN;
        requires d.exp + 1 + t.exp == LOGN;
    {
        var j := 0;
        var u := 0;

        ghost var blocks := seq(d.full, n requires 0 <= n < d.full => []);

        while (j < t.full)
            invariant 0 <= u == (2 * d.full) * j;
        {
            P_table_index_bounded(t, j);
            var w := P()[t.full + j]; // psi_t * w_t^bitrev(j)

            ghost var prev_u := u;
            ghost var prev_j := j;

            slice_loop(u, d, w, j, blocks);
            j := j + 1;
            u := u + 2 * d.full;

            calc == {
                u;
                prev_u + 2 * d.full;
                2 * d.full * prev_j + 2 * d.full;
                {
                    LemmaMulIsDistributive(2 * d.full, prev_j, 1);
                }
                (2 * d.full) * (prev_j + 1);
            }
        }
    }

    method mulntt_ct()
    {
        var d := pow2(LOGN);
        var t := pow2(0);
        Nth_root_lemma();

        while (t.full < N)
            invariant d.exp + t.exp == LOGN;
            invariant t.exp <= LOGN;
        {
            d := pow2_half(d);

            // assert d.exp + 1 + t.exp == LOGN;
            // assume d.full * 2 * t.full == N;
            level_loop(t, d);
            t := pow2_double(t);
        }
    }
}