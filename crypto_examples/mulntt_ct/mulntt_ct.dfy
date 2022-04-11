include "nth_root.dfy"
include "mulntt_ct_rec.dfy"

module ntt {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul

    import opened pows_of_2
    import opened omegas

    import opened mulntt_ct_rec
    // import opened ntt_recs
    // import opened rindex
    // import opened bins
    // import opened polys

    function method block_count(m: pow2_t): nat
        requires 0 <= m.exp <= LOGN;
    {
        pow2_div(pow2(LOGN), m).full
    }

    lemma block_count_product_lemma(m: pow2_t)
        requires 0 <= m.exp <= LOGN;
        ensures block_count(m) * m.full == N;
    {
        Nth_root_lemma();
    }

    lemma block_count_half_lemma(m: pow2_t)
        requires 1 <= m.exp <= LOGN;
        ensures block_count(pow2_half(m)) == block_count(m) * 2;
    {
        Nth_root_lemma();
        var left := pow2_div(pow2(LOGN), pow2_half(m));
        assert left.full * (m.full / 2) == N;
        var right := pow2_div(pow2(LOGN), m);
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

    type n_sized = s: seq<elem>
        | |s| == N == pow2(LOGN).full witness *

    function method A(): n_sized

    function method P(): n_sized

    lemma A_table_index_bounded_lemma(s: nat, d: pow2_t, j: nat, t: pow2_t)
        requires 0 <= d.exp < LOGN;
        requires 0 <= t.exp < LOGN;
        requires block_count(t) == 2 * d.full;
        // requires block_count(pow2_double(t)) == d.full;
        requires j < t.full;
        requires s < (2 * d.full) * j + d.full;
        ensures s + d.full < N;
    {
        assume false;
        // block_count_product_lemma(t);
        // assert block_count(t) * t.full == N;
    }

    datatype slice_loop_view = slice_loop_view(
        lower: lpolys,
        higher: lpolys)
    {
        predicate slice_view_wf()
        {
            && higher.level_wf()
            && lower.level_wf()
            && 1 <= higher.bsize.exp <= LOGN
            && higher.build_smaller_level() == lower
        }
    }

    // predicate slice_loop_inv()

    function bit_rev_int(j: nat, bound: pow2_t): nat

    method slice_loop(
        a: n_sized,
        u: nat,
        d: pow2_t,
        w: elem,
        ghost j: nat,
        ghost t: pow2_t)
        // ghost sv: slice_loop_view)

    returns (new_a: n_sized)
    
    // ghost new_blocks: seq<seq<elem>>)
        // requires |blocks| == d.full;
        requires 0 <= t.exp < LOGN;
        requires 0 <= d.exp < LOGN;

        requires 2 * d.full * bit_rev_int(j, t) >= 0;

        requires block_count(t) == 2 * d.full;
        // d blocks, each of 2t size 
        // requires block_count(pow2_double(t)) == d.full;
        requires j < t.full;
        requires u == (2 * d.full) * j;
        // requires t.exp == 0 ==> a == A();

        // ensures |new_blocks| == d.full;
    {
        var s := u;
        // new_blocks := blocks;
        new_a := a;

        assume w == modpow(PSI, 2 * d.full * bit_rev_int(j, t) + d.full);

        while (s < u + d.full)
            // invariant |new_blocks| == |blocks|;
            // invariant 
        {
            A_table_index_bounded_lemma(s, d, j, t);
            ghost var b_idx := s - u;
            var e := a[s];
            var o := a[s + d.full];

            // assume e == 

            var x := modmul(o, w);
            new_a := new_a[s+d.full := modsub(e, x)];
            new_a := new_a[s := modadd(e, x)];

            s := s + 1;
            // new_blocks := new_blocks[b_idx := blocks[b_idx]];
        }
    }

    lemma P_table_index_bounded_lemma(t: pow2_t, j: nat)
        requires t.exp < LOGN;
        requires j < t.full;
        ensures t.full + j < N;
    {
        assume false;
    }

    // method level_loop(a: n_sized, t: pow2_t, d: pow2_t)
    //     requires t.exp < LOGN;
    //     requires d.exp + 1 + t.exp == LOGN;
    //     requires block_count(pow2_double(t)) == d.full;
    //     requires block_count(t) == 2 * d.full;
    // {
    //     var j := 0;
    //     var u := 0;

    //     ghost var blocks := seq(d.full, n requires 0 <= n < d.full => []);

    //     while (j < t.full)
    //         invariant 0 <= u == (2 * d.full) * j;
    //         invariant |blocks| == d.full;
    //     {
    //         P_table_index_bounded_lemma(t, j);
    //         var w := P()[t.full + j]; // psi_t * w_t^bitrev(j)

    //         ghost var prev_u := u;
    //         ghost var prev_j := j;

    //         blocks := slice_loop(u, d, w, j, t, blocks);
    //         j := j + 1;
    //         u := u + 2 * d.full;

    //         calc == {
    //             u;
    //             prev_u + 2 * d.full;
    //             2 * d.full * prev_j + 2 * d.full;
    //             {
    //                 LemmaMulIsDistributive(2 * d.full, prev_j, 1);
    //             }
    //             (2 * d.full) * (prev_j + 1);
    //         }
    //     }
    // }

    // method mulntt_ct()
    // {
    //     var d := pow2(LOGN);
    //     var t := pow2(0);
    //     Nth_root_lemma();

    //     while (t.full < N)
    //         invariant d.exp + t.exp == LOGN;
    //         invariant t.exp <= LOGN;
    //         invariant block_count(t) == d.full;
    //     {
    //         d := pow2_half(d);

    //         block_count_half_lemma(pow2_double(t));
    //         // assert block_count(pow2_double(t)) == d.full;
    //         // assert block_count(t) == 2 * d.full;

    //         // assert d.exp + 1 + t.exp == LOGN;
    //         // assume d.full * 2 * t.full == N;
    //         level_loop(t, d);
    //         t := pow2_double(t);
    //         // block_count_half_lemma(t);
    //     }
    // }
}