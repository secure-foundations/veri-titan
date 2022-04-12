include "nth_root.dfy"
include "ntt_index.dfy"
include "polys.dfy"

module mulntt_ct_rec {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul

    import opened pows_of_2

    import opened nth_root
    import opened ntt_index

    function method A(): seq<elem>
        ensures |A()| == N == pow2(LOGN).full;

    function method block_count(m: pow2_t): nat
        requires 0 <= m.exp <= LOGN;
    {
        pow2_div(pow2(LOGN), m).full
    }

    // lemma block_count_product_lemma(m: pow2_t)
    //     requires 0 <= m.exp <= LOGN;
    //     ensures block_count(m) * m.full == N;
    // {
    //     Nth_root_lemma();
    // }

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
    
    lemma point_view_index_bound_lemma(i: nat, j: nat, bsize: pow2_t)
        requires bsize.exp <= LOGN;
        requires i < block_count(bsize);
        requires j < bsize.full;
        ensures 0 <= i + j * block_count(bsize) < N;
    {
        var count := block_count(bsize);
        calc {
            i + j * count;
            <=
            count - 1 + j * count;
            <= { LemmaMulInequality(j, bsize.full - 1, count); }
            count - 1 + (bsize.full - 1) * count;
            { LemmaMulIsDistributive(count, bsize.full, 1); }
            count - 1 + bsize.full * count - count;
            bsize.full * count - 1;
            { Nth_root_lemma(); }
            N - 1;
        }

        LemmaMulStrictlyPositiveAuto();
    }

    function point_view_index(i: nat, j: nat, bsize: pow2_t): (offset: nat)
        requires bsize.exp <= LOGN;
        requires i < block_count(bsize);
        requires j < bsize.full;
        ensures offset < N;
    {
        point_view_index_bound_lemma(i, j, bsize);
        i + j * block_count(bsize)
    }

    function points_view(a: n_sized, i: nat, bsize: pow2_t): (v: seq<elem>)
        requires bsize.exp <= LOGN;
        requires i < block_count(bsize);
        // ensures |v| == bsize.full;
    {
        var size := bsize.full;
        seq(size, j requires 0 <= j < size => a[point_view_index(i, j, bsize)])
    }

    // interpret an n_sized buffer as a level view
    // contains blocks of points, each block has bsize
    function level_points_view(a: n_sized, bsize: pow2_t): (vs: seq<seq<elem>>)
        requires bsize.exp <= LOGN;
        ensures unifromly_sized(vs, bsize);
    {
        var count := block_count(bsize);
        var vs := seq(count, i requires 0 <= i < count => points_view(a, i, bsize));
        assert unifromly_sized(vs, bsize) by {
            reveal unifromly_sized();
        }
        vs
    }

    function method {:opaque} build_lower_level(higher: seq<seq<elem>>, bsize: pow2_t): (lower: seq<seq<elem>>)
        requires 1 <= bsize.exp <= LOGN;
        requires unifromly_sized(higher, bsize);
        ensures unifromly_sized(lower, pow2_half(bsize));
    {
        reveal unifromly_sized();
        pow2_basics(bsize);
        block_count_half_lemma(bsize);
        var new_size := pow2_half(bsize);
        var new_count := |higher| * 2;
        seq(new_count, n requires 0 <= n < new_count => 
            if n % 2 == 0 then even_indexed_items(higher[n/2], bsize)
            else odd_indexed_items(higher[n/2], bsize))
    }

    lemma base_level_correct()
        ensures unifromly_sized([A()], pow2(LOGN));
    {
        reveal unifromly_sized();
    }

    // construct polys level view 
    // each block is a poly, has bsize coefficients
    function level_polys(bsize: pow2_t): (lps: seq<seq<elem>>)
        requires 1 <= bsize.exp <= LOGN;
        decreases LOGN - bsize.exp;
        ensures unifromly_sized(lps, bsize);
    {
        if bsize.exp == LOGN then
            base_level_correct();
            [A()]
        else
            assert 1 <= bsize.exp <= LOGN;
            var double_size := pow2_double(bsize);
            assert 1 <= double_size.exp <= LOGN;
            var higher := level_polys(double_size);
            build_lower_level(higher, double_size)
    }

    lemma level_polys_index_correspondence_lemma(
        higher: seq<seq<elem>>, hi_size: pow2_t, i: nat, 
        lower: seq<seq<elem>>)
        requires 1 <= hi_size.exp <= LOGN;
        requires i < |higher|;
        requires unifromly_sized(higher, hi_size);
        requires build_lower_level(higher, hi_size) == lower;
        ensures |higher[i]| == hi_size.full;
        ensures 2 * i + 1 < |lower|;
        ensures even_indexed_items(higher[i], hi_size) == lower[2 * i];
        ensures odd_indexed_items(higher[i], hi_size) == lower[2 * i + 1];
        ensures |lower[2 * i]| == |lower[2 * i + 1]| == pow2_half(hi_size).full;
    {
        reveal unifromly_sized();
        reveal build_lower_level();
    }
}