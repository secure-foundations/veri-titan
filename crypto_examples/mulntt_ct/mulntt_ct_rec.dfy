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
    import opened ntt_polys

    function method A(): seq<elem>
        ensures |A()| == N == pow2(LOGN).full;

    function method block_count(m: pow2_t): pow2_t
        requires 0 <= m.exp <= LOGN;
    {
        pow2_div(pow2(LOGN), m)
    }

    function method block_size(c: pow2_t): pow2_t
        requires 0 <= c.exp <= LOGN;
    {
        pow2_div(pow2(LOGN), c)
    }

    // lemma block_count_product_lemma(m: pow2_t)
    //     requires 0 <= m.exp <= LOGN;
    //     ensures block_count(m) * m.full == N;
    // {
    //     Nth_root_lemma();
    // }

    lemma block_count_half_lemma(m: pow2_t)
        requires 1 <= m.exp <= LOGN;
        ensures block_count(pow2_half(m)) == pow2_double(block_count(m));
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

    predicate {:opaque} unifromly_sized(blocks: seq<seq<elem>>, bsize: pow2_t)
        requires bsize.exp <= LOGN;
        ensures unifromly_sized(blocks, bsize)
            ==> |blocks| == block_count(bsize).full;
    {
        && (forall i: nat | i < |blocks| :: |blocks[i]| == bsize.full)
        && |blocks| == block_count(bsize).full
    }


    type n_sized = s: seq<elem>
        | |s| == N == pow2(LOGN).full witness *
    
    lemma point_view_index_bound_lemma(i: nat, j: nat, bsize: pow2_t)
        requires bsize.exp <= LOGN;
        requires i < block_count(bsize).full;
        requires j < bsize.full;
        ensures 0 <= i + j * block_count(bsize).full < N;
    {
        var count := block_count(bsize).full;
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
        requires i < block_count(bsize).full;
        requires j < bsize.full;
        ensures offset < N;
    {
        point_view_index_bound_lemma(i, j, bsize);
        i + j * block_count(bsize).full
    }

    function points_view(a: n_sized, i: nat, bsize: pow2_t): (v: seq<elem>)
        requires bsize.exp <= LOGN;
        requires i < block_count(bsize).full;
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
        var count := block_count(bsize).full;
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

    function bit_rev_int(i: nat, bound: pow2_t): (j: nat)
        requires i < bound.full;
        ensures j < bound.full;

    // d is the block count
    function x_value(i: nat, d: pow2_t): elem
        requires d.exp <= LOGN;
        requires i < block_size(d).full;
    {
        var bound := pow2_div(pow2(LOGN), d);
        LemmaMulNonnegative(d.full, bit_rev_int(i, bound));
        modmul(modpow(OMEGA, d.full * bit_rev_int(i, bound)), modpow(PSI, d.full))
    }

    // d is the block count
    predicate {:opaque} points_eval_prefix_inv(points: seq<elem>, poly: seq<elem>, l: nat, d: pow2_t)
    {
        && d.exp <= LOGN
        && l <= |points| == |poly| == block_size(d).full
        && forall i | 0 <= i < l :: poly_eval(poly, x_value(i, d)) == points[i]
    }

    // d is the block count
    predicate {:opaque} points_eval_suffix_inv(points: seq<elem>, poly: seq<elem>, l: nat, d: pow2_t)
    {
        && d.exp <= LOGN
        && l <= |points| == |poly| == block_size(d).full
        && forall i | l <= i < block_size(d).full ::
            poly_eval(poly, x_value(i, d)) == points[i]
    }

    datatype s_loop_view = s_loop_view(
        lower: seq<seq<elem>>, // lower polys
        higher: seq<seq<elem>>, // higher polys
        hsize: pow2_t)
    {
        predicate s_loop_wf()
        {
            && 1 <= hsize.exp <= LOGN
            && unifromly_sized(higher, hsize)
            && build_lower_level(higher, hsize) == lower
        }

        function lsize(): pow2_t
            requires s_loop_wf();
        {
            pow2_half(hsize)
        }

        function lcount(): pow2_t
            requires s_loop_wf();
        {
            block_count(lsize())
        }

        function hcount(): pow2_t
            requires s_loop_wf();
        {
            block_count(hsize)
        }

        lemma size_count_lemma()
            requires s_loop_wf();
            ensures pow2_double(lsize()) == hsize;
            ensures lcount() == pow2_double(hcount());
            ensures lcount().full * lsize().full
                == hcount().full * hsize.full == N;
        {
            Nth_root_lemma();
            block_count_half_lemma(hsize);
        }

        predicate {:opaque} s_loop_higher_inv(a: n_sized, hcount: pow2_t, j: nat, bi: nat)
            requires hcount.exp <= LOGN;
            requires bi < hcount.full;
            requires s_loop_wf();
            requires hsize == block_size(hcount);
        {
            && var hpoints := level_points_view(a, hsize);
            && (forall i | 0 <= i < bi ::
                points_eval_prefix_inv(hpoints[i], higher[bit_rev_int(i, hcount)], 2*j+2, hcount))
            && (forall i | bi <= i < hcount.full ::
                points_eval_prefix_inv(hpoints[i], higher[bit_rev_int(i, hcount)], 2*j, hcount))
        }

        predicate {:opaque} s_loop_lower_inv(a: n_sized, hcount: pow2_t, j: nat, bi: nat)
            requires hcount.exp <= LOGN;
            requires bi < hcount.full;
            requires s_loop_wf();
            requires hsize == block_size(hcount);
        {
            size_count_lemma();
            && var lcount := lcount();
            && var lpoints := level_points_view(a, lsize());
            && (forall i | (0 <= i < bi || hcount.full <= i < bi + hcount.full) ::
                && (points_eval_suffix_inv(lpoints[i], lower[bit_rev_int(i, lcount)], j+1, lcount)))
            && (forall i | (bi <= i < hcount.full || bi + hcount.full <= i < lcount.full) ::
                points_eval_suffix_inv(lpoints[i], lower[bit_rev_int(i, lcount)], j, lcount))
        }

        predicate s_loop_inv(a: n_sized, hcount: pow2_t, j: nat, bi: nat)
        {
            && s_loop_wf()
            && hcount.exp <= LOGN
            && bi < hcount.full
            && j < lsize().full
            && hsize == block_size(hcount)
            && s_loop_higher_inv(a, hcount, j, bi)
            && s_loop_lower_inv(a, hcount, j, bi)
        }

        lemma higher_points_view_index_lemma(a: n_sized, hcount: pow2_t, j: nat, bi: nat, s: nat)
            requires s_loop_inv(a, hcount, j, bi);
            requires s == bi + (2*j) * hcount.full;
            ensures s + hcount.full < N;
            ensures a[s] == level_points_view(a, hsize)[bi][2*j];
            ensures a[s+hcount.full] == level_points_view(a, hsize)[bi][2*j+1];
        {
            size_count_lemma();
            var hpoints := level_points_view(a, hsize);

            calc == {
                hpoints[bi][2*j];
                points_view(a, bi, hsize)[2*j];
                a[point_view_index(bi, 2*j, hsize)];
                {
                    assert s == point_view_index(bi, 2*j, hsize);
                }
                a[s];
            }

            calc == {
                s + hcount.full;
                point_view_index(bi, 2*j, hsize) + hcount.full;
                bi + (2*j) * hcount.full + hcount.full;
                {
                    LemmaMulIsDistributiveAddOtherWayAuto();
                }
                bi + (2*j+1) * hcount.full;
                point_view_index(bi, 2*j+1, hsize);
            }

            calc == {
                hpoints[bi][2*j+1];
                points_view(a, bi, hsize)[2*j+1];
                a[point_view_index(bi, 2*j+1, hsize)];
                a[s + hcount.full];
            }
        }

        lemma lower_points_view_index_lemma(a: n_sized, hcount: pow2_t, j: nat, bi: nat, s: nat)
            requires s_loop_inv(a, hcount, j, bi);
            requires s == bi + (2*j) * hcount.full;
            ensures s + hcount.full < N;
            ensures bi + hcount.full < lcount().full;
            ensures a[s] == level_points_view(a, lsize())[bi][j];
            ensures a[s+hcount.full] == level_points_view(a, lsize())[bi+hcount.full][j];
        {
            size_count_lemma();
            var lpoints := level_points_view(a, lsize());

            calc == {
                s;
                bi + (2*j) * hcount.full;
                {
                    LemmaMulIsAssociativeAuto();
                }
                bi + j * (2*hcount.full);
                point_view_index(bi, j, lsize());
            }

            calc == {
                lpoints[bi][j];
                points_view(a, bi, lsize())[j];
                a[point_view_index(bi, j, lsize())];
                a[s];
            }

            calc == {
                s + hcount.full;
                bi + hcount.full + (j*2) * hcount.full;
                {
                    LemmaMulIsAssociativeAuto();
                }
                bi + hcount.full + j * (2 * hcount.full);
                bi + hcount.full + j * lcount().full;
                point_view_index(bi +  hcount.full, j, lsize());
            }

            calc == {
                lpoints[bi+hcount.full][j];
                points_view(a, bi+hcount.full, lsize())[j];
                a[point_view_index(bi+hcount.full, j, lsize())];
                a[s+hcount.full];
            }
        }

        // lemma s_loop_inv_preserved(a: n_sized, a': n_sized, hcount: pow2_t, j: nat, bi: nat)
        //     requires s_loop_inv(a, hcount, j, bi);
        // {


        // }
    }
    // function level_points_view(a: n_sized, bsize: pow2_t): (vs: seq<seq<elem>>)

}