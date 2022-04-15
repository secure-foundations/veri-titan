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

    lemma point_view_index_disjont_lemma(i: nat, j: nat, i': nat, j': nat, bsize: pow2_t)
        requires bsize.exp <= LOGN;
        requires i < block_count(bsize).full;
        requires j < bsize.full;
        requires i' < block_count(bsize).full;
        requires j' < bsize.full;
        requires i != i' || j != j';
        ensures point_view_index(i, j, bsize) != point_view_index(i', j', bsize);
    {
        var offset := point_view_index(i, j, bsize);
        var offset' := point_view_index(i', j', bsize);
        var count := block_count(bsize).full;

        if i != i' && offset == offset' {
            LemmaFundamentalDivModConverse(offset, count, j, i);
            LemmaFundamentalDivModConverse(offset, count, j', i');
            assert false;
            return;
        }

        if j != j' && offset == offset' {
            assert i == i';
            assert j * count == j' * count;
            LemmaMulIsCommutativeAuto();
            LemmaMulEqualityConverse(count, j', j);
            assert false;
        }
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

    function split_bits(i: nat, bound: pow2_t): (r: (nat, nat))
        requires i < bound.full;
        requires bound.exp > 0;
        ensures r.0 == 0 || r.0 == 1;
        ensures r.0 * pow2_half(bound).full + r.1 == i;
    {
        var half_bound := pow2_half(bound);
        var msbv := i/half_bound.full;
        var reaminder := i % half_bound.full;
        LemmaFundamentalDivMod(i, half_bound.full);

        assert msbv == 0 || msbv == 1 by {
            if msbv > 1 {
                calc {
                    i;
                    msbv * half_bound.full + reaminder;
                    >= { LemmaMulInequalityAuto(); }
                    2 * half_bound.full + reaminder;
                    bound.full + reaminder;
                }
                assert false;
            }
            LemmaDivBasicsAuto();
        }
        (msbv, reaminder)
    }

    function {:opaque} bit_rev_int(i: nat, bound: pow2_t): (ri: nat)
        requires i < bound.full;
        ensures ri < bound.full;
        decreases bound.exp;
    {
        if bound.exp == 0 then
            0
        else
            var half_bound := pow2_half(bound);
            var (msb, rest):= split_bits(i, bound);
            var ri := msb + bit_rev_int(rest, half_bound) * 2;
            ri
    }

    lemma bit_rev_int_lemma(i: nat, bound: pow2_t)
        requires i < bound.full;
        ensures bit_rev_int(i, pow2_double(bound)) == 2 * bit_rev_int(i, bound);
        ensures bit_rev_int(i+bound.full, pow2_double(bound)) == 2 * bit_rev_int(i, bound) + 1;
    {
        reveal bit_rev_int();
        var ri := bit_rev_int(i, bound);
        var dbound := pow2_double(bound);
        var dri := bit_rev_int(i, dbound);
        var (msbi, _):= split_bits(i, dbound);

        assert i % bound.full == i by {
            LemmaSmallMod(i, bound.full);
        }

        assert dri == 2 * ri by {
            assert msbi == 0;
        }

        var j := i + bound.full;
        var drj := bit_rev_int(j, dbound);
        var (msbj, _):= split_bits(j, dbound);

        assert drj == 2 * ri + 1 by {
            assert msbj == 1; 
        }
    }

    // d is the block count
    // i is the offset in the block
    function x_value(i: nat, d: pow2_t): elem
        requires d.exp <= LOGN;
        requires i < block_size(d).full;
    {
        var bound := block_size(d);
        LemmaMulNonnegative(bit_rev_int(i, bound), d.full);
        LemmaMulIsAssociative(2, bit_rev_int(i, bound), d.full);
        // modmul(modpow(OMEGA, d.full * (i, bound)), modpow(PSI, d.full))bit_rev_int
        modpow(PSI, 2 * bit_rev_int(i, bound) * d.full + d.full)
    }

    predicate {:opaque} points_eval_prefix_inv(points: seq<elem>, poly: seq<elem>, l: nat, count: pow2_t)
    {
        && count.exp <= LOGN
        && l <= |points| == |poly| == block_size(count).full
        && forall i | 0 <= i < l :: poly_eval(poly, x_value(i, count)) == points[i]
    }

    // d is the block count
    predicate {:opaque} points_eval_suffix_inv(points: seq<elem>, poly: seq<elem>, l: nat, count: pow2_t)
    {
        && count.exp <= LOGN
        && l <= |points| == |poly| == block_size(count).full
        && forall i | l <= i < block_size(count).full ::
            poly_eval(poly, x_value(i, count)) == points[i]
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

        lemma x_value_even_square_lemma(j: nat, x: elem)
            requires s_loop_wf();
            requires 2 * j < hsize.full;
            requires x == x_value(2 * j, hcount());
            ensures modmul(x, x) == x_value(j, lcount());
        {
            size_count_lemma();
            var hc := hcount();

            LemmaMulNonnegative(bit_rev_int(2 * j, hsize), hc.full);
            LemmaMulIsAssociative(2, bit_rev_int(2 * j, hsize), hc.full);
            var exp := 2 * bit_rev_int(2 * j , hsize) * hc.full + hc.full;

            calc == {
                2 * exp;
                2 * (2 * bit_rev_int(2 * j , hsize) * hc.full + hc.full);
                {
                    LemmaMulIsDistributive(2, 2 * bit_rev_int(2 * j , hsize) * hc.full, hc.full);
                }
                2 * (2 * bit_rev_int(2 * j , hsize) * hc.full) + 2 * hc.full;
                2 * (2 * bit_rev_int(2 * j , hsize) * hc.full) + lcount().full;
                {
                    LemmaMulIsCommutative(2, bit_rev_int(2 * j , hsize));
                }
                2 * (bit_rev_int(2 * j , hsize) * 2 * hc.full) + lcount().full;
                {
                    LemmaMulIsAssociative(bit_rev_int(2 * j , hsize), 2, hc.full);
                }
                2 * (bit_rev_int(2 * j , hsize) * (2 * hc.full)) + lcount().full;
                2 * (bit_rev_int(2 * j , hsize) * lcount().full) + lcount().full;
                {
                    LemmaMulIsAssociative(2, bit_rev_int(2 * j , hsize), lcount().full);
                }
                2 * bit_rev_int(2 * j , hsize) * lcount().full + lcount().full;
                {
                    assume bit_rev_int(2 * j , hsize) == bit_rev_int(j, lsize());
                }
                2 * bit_rev_int(j , lsize()) * lcount().full + lcount().full;
            }
    
            var temp := Pow(PSI, exp);
    
            calc == {
                modmul(x, x);
                ((temp % Q) * (temp % Q)) % Q;
                {
                    LemmaMulModNoopGeneral(temp, temp, Q);
                }
                (temp * temp) % Q;
                {
                    LemmaPowAdds(PSI, exp, exp);
                }
                Pow(PSI, 2 * exp) % Q;
                x_value(j, lcount());
            }
        }

        lemma x_value_odd_square_lemma(j: nat, x: elem)
            requires s_loop_wf();
            requires 2 * j < hsize.full;
            requires x == x_value(2 * j + 1, hcount());
            ensures modmul(x, x) == x_value(j, lcount());
        {
            size_count_lemma();
            var hc := hcount();

            LemmaMulNonnegative(bit_rev_int(2 * j + 1, hsize), hc.full);
            LemmaMulIsAssociative(2, bit_rev_int(2 * j + 1, hsize), hc.full);
            var exp := 2 * bit_rev_int(2 * j + 1, hsize) * hc.full + hc.full;   

            var temp := Pow(PSI, exp);
    
            // calc == {
            //     2 * exp;
            //     2 * (2 * bit_rev_int(2 * j + 1, hsize) * hc.full + hc.full);
            //     {
            //         LemmaMulIsDistributive(2, 2 * bit_rev_int(2 * j + 1, hsize) * hc.full, hc.full);
            //     }
            //     2 * (2 * bit_rev_int(2 * j + 1, hsize) * hc.full) + 2 * hc.full;
            //     2 * (2 * bit_rev_int(2 * j + 1, hsize) * hc.full) + lcount().full;
            //     {
            //         LemmaMulIsCommutative(2, bit_rev_int(2 * j + 1, hsize));
            //     }
            //     2 * (bit_rev_int(2 * j + 1, hsize) * 2 * hc.full) + lcount().full;
            //     {
            //         LemmaMulIsAssociative(bit_rev_int(2 * j + 1, hsize), 2, hc.full);
            //     }
            //     2 * (bit_rev_int(2 * j + 1, hsize) * (2 * hc.full)) + lcount().full;
            //     2 * (bit_rev_int(2 * j + 1, hsize) * lcount().full) + lcount().full;
            //     {
            //         LemmaMulIsAssociative(2, bit_rev_int(2 * j + 1, hsize), lcount().full);
            //     }
            //     2 * bit_rev_int(2 * j + 1, hsize) * lcount().full + lcount().full;
            // }

            calc == {
                modmul(x, x);
                ((temp % Q) * (temp % Q)) % Q;
                {
                    LemmaMulModNoopGeneral(temp, temp, Q);
                }
                (temp * temp) % Q;
                {
                    LemmaPowAdds(PSI, exp, exp);
                }
                Pow(PSI, 2 * exp) % Q;
            }

            assume false;         
        }

        predicate {:opaque} s_loop_higher_inv(a: n_sized, hcount: pow2_t, j: nat, bi: nat)
            requires hcount.exp <= LOGN;
            requires bi <= hcount.full;
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
            // && (forall i | (0 <= i < bi || hcount.full <= i < bi + hcount.full) ::
            //     && (points_eval_suffix_inv(lpoints[i], lower[bit_rev_int(i, lcount)], j+1, lcount)))
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

        // lemma s_loop_index_bound(a: n_sized, hcount: pow2_t, j: nat, bi: nat)
        //     requires s_loop_wf();
        //     requires hcount.exp <= LOGN;
        //     requires bi < hcount.full;
        //     requires j < lsize().full;
        //     requires hsize == block_size(hcount);
        //     ensures bi + (2*j) * hcount.full + hcount.full < N;
        //     ensures bi + hcount.full < lcount().full;
        // {
        //     size_count_lemma();
        //     point_view_index_bound_lemma(bi, 2 * j+1, hsize);
        //     LemmaMulIsDistributive(hcount.full, 2*j, 1);
        //     assert (2*j) * hcount.full + hcount.full == (2*j + 1) * hcount.full;
        // }

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

        function get_even_poly(bi: nat): seq<elem>
            requires s_loop_wf();
            requires bi < lcount().full;
        {
            lower[bit_rev_int(bi, lcount())]
        }

        function get_odd_poly(bi: nat): seq<elem>
            requires s_loop_wf();
            requires bi + hcount().full < lcount().full;
        {
            lower[bit_rev_int(bi+hcount().full, lcount())]
        }

        function get_full_poly(bi: nat): seq<elem>
            requires s_loop_wf();
            requires bi < hcount().full;
        {
            higher[bit_rev_int(bi, hcount())]
        }
    
        lemma lower_points_view_value_lemma(a: n_sized, hcount: pow2_t, j: nat, bi: nat, s: nat)
            requires s_loop_inv(a, hcount, j, bi);
            requires s == bi + (2*j) * hcount.full;
            ensures s + hcount.full < N;
            ensures bi + hcount.full < lcount().full;
            ensures a[s] == poly_eval(get_even_poly(bi), x_value(j, lcount()));
            ensures a[s+hcount.full] == poly_eval(get_odd_poly(bi), x_value(j, lcount()));
        {
            size_count_lemma();
            lower_points_view_index_lemma(a, hcount, j, bi, s);
            var lpoints := level_points_view(a, lsize());
            var lcount := lcount();

            var e_poly := get_even_poly(bi);
            var e_points := lpoints[bi];

            assert a[s] == poly_eval(e_poly, x_value(j, lcount)) by {
                assert points_eval_suffix_inv(e_points, e_poly, j, lcount) by {
                    reveal s_loop_lower_inv();
                }
                reveal points_eval_suffix_inv();
                assert a[s] == e_points[j];
            }

            var o_poly := get_odd_poly(bi);
            var o_points := lpoints[bi+hcount.full];

            assert a[s+hcount.full] == poly_eval(o_poly, x_value(j, lcount)) by {
                assert points_eval_suffix_inv(o_points, o_poly, j, lcount) by {
                    reveal s_loop_lower_inv();
                }
                reveal points_eval_suffix_inv();
                assert a[s+hcount.full] == lpoints[bi+hcount.full][j];
            }
        }

        lemma level_polys_bitrev_index_correspondence_lemma(a: n_sized, hcount: pow2_t, j: nat, bi: nat)
            requires s_loop_inv(a, hcount, j, bi);
            ensures |get_full_poly(bi)| == hsize.full;
            ensures bi + hcount.full < lcount().full;
            ensures get_even_poly(bi) == even_indexed_items(get_full_poly(bi), hsize);
            ensures get_odd_poly(bi) == odd_indexed_items(get_full_poly(bi), hsize);
        {
            size_count_lemma();

            var ri := bit_rev_int(bi, hcount);
            var poly := higher[ri];

            level_polys_index_correspondence_lemma(higher, hsize, ri, lower);

            assert even_indexed_items(poly, hsize) == lower[2 * ri];
            assert odd_indexed_items(poly, hsize) == lower[2 * ri + 1];

            bit_rev_int_lemma(bi, hcount);
            assert bit_rev_int(bi, lcount()) == 2 * ri;
            assert bit_rev_int(bi + hcount.full, lcount()) == 2 * ri + 1;
        }

        lemma ct_butterfly_even_lemma(a: n_sized, hcount: pow2_t, j: nat, bi: nat, s: nat, w: elem)
            requires s_loop_inv(a, hcount, j, bi);
            requires s == bi + (2*j) * hcount.full;
            requires w == x_value(2 * j, hcount);
            ensures s + hcount.full < N;
            ensures bi + hcount.full < lcount().full;
            ensures poly_eval(get_full_poly(bi), w) == modadd(a[s], modmul(a[s+hcount.full], w));
        {
            size_count_lemma();
            lower_points_view_value_lemma(a, hcount, j, bi, s);
            var e := a[s];
            var o := a[s+hcount.full];
            var p := modmul(o, w);

            var sum := modadd(e, p);
            var diff := modsub(e, p);

            var e_poly := get_even_poly(bi);
            var o_poly := get_odd_poly(bi);
            var f_poly := get_full_poly(bi);

            level_polys_bitrev_index_correspondence_lemma(a, hcount, j, bi);

            var x := w;
            var sqr := x_value(j, lcount());

            assert e == poly_eval(e_poly, sqr);
            assert o == poly_eval(o_poly, sqr);

            x_value_even_square_lemma(j, x);

            poly_eval_split_lemma(f_poly, e_poly, o_poly, hsize, x);
        }
        
        lemma ct_butterfly_odd_lemma(a: n_sized, hcount: pow2_t, j: nat, bi: nat, s: nat, w: elem)
            requires s_loop_inv(a, hcount, j, bi);
            requires s == bi + (2*j) * hcount.full;
            requires w == x_value(2 * j, hcount);
            ensures s + hcount.full < N;
            ensures bi + hcount.full < lcount().full;
            ensures poly_eval(get_full_poly(bi), x_value(2*j+1, hcount))
                == modsub(a[s], modmul(a[s+hcount.full], w));
        {
            size_count_lemma();
            lower_points_view_value_lemma(a, hcount, j, bi, s);
            var e := a[s];
            var o := a[s+hcount.full];
            var p := modmul(o, w);

            var diff := modsub(e, p);

            var e_poly := get_even_poly(bi);
            var o_poly := get_odd_poly(bi);
            var f_poly := get_full_poly(bi);

            var x_o := x_value(2*j+1, hcount);
        
            x_value_odd_square_lemma(j, x_o);

            level_polys_bitrev_index_correspondence_lemma(a, hcount, j, bi);

            var sqr := x_value(j, lcount());

            // assert e == poly_eval(e_poly, sqr);
            // assert o == poly_eval(o_poly, sqr);

            assume x_o == Q - w;

            calc == {
                diff;
                modsub(e, modmul(o, w));
                {
                    LemmaMulNonnegative(o, w);
                }
                (e as int - ((o * w) % Q)) % Q;
                {
                    LemmaSubModNoopRight(e, o * w, Q);
                }
                (e as int - (o * w)) % Q;
                (e as int - ((o * (Q - x_o)))) % Q;
                {
                    LemmaMulIsCommutative(o, Q - x_o);
                }
                (e as int - (((Q - x_o) * o))) % Q;
                {
                    LemmaMulIsDistributive(o, Q, x_o);
                }
                (e as int - (Q * o- x_o * o)) % Q;
                (e as int + x_o * o - Q * o) % Q;
                {
                    LemmaModMultiplesVanish(e as int + x_o * o, -(o as int), Q);
                }
                (e as int + x_o * o) % Q;
                {
                    LemmaAddModNoop(e, x_o * o, Q);
                }
                ((e % Q) + (x_o * o) % Q) % Q;
                modadd(e, modmul(x_o, o));
                modadd(poly_eval(e_poly, sqr), modmul(x_o, poly_eval(o_poly, sqr)));
                {
                    poly_eval_split_lemma(f_poly, e_poly, o_poly, hsize, x_o);
                }
                poly_eval(f_poly, x_o);
            }
        }

        predicate s_loop_update(a: n_sized, a': n_sized, hcount: pow2_t, j: nat, bi: nat)
            requires s_loop_inv(a, hcount, j, bi);
        {
            var s := bi + (2*j) * hcount.full;
            var w := x_value(2 * j, hcount);
            point_view_index_bound_lemma(bi, 2 * j+1, hsize);
            point_view_index_bound_lemma(bi, 2 * j, hsize);
            LemmaMulIsDistributive(hcount.full, 2*j, 1);
            assert (2*j) * hcount.full + hcount.full == (2*j + 1) * hcount.full;
            var s' := s+hcount.full; 
            a' == a[s := modadd(a[s], modmul(a[s'], w))]
                [s' := modsub(a[s], modmul(a[s'], w))]
        }

        lemma s_loop_perserves_higher_inv_lemma(a: n_sized, a': n_sized, hcount: pow2_t, j: nat, bi: nat)
            requires s_loop_inv(a, hcount, j, bi);
            requires s_loop_update(a, a', hcount, j, bi);
            ensures s_loop_higher_inv(a', hcount, j, bi+1);
        {
            reveal s_loop_higher_inv();
            var s := bi + (2*j) * hcount.full;
            assert s == point_view_index(bi, 2*j, hsize);
            var s' := s+hcount.full; 
            assume s' == bi + (2*j + 1) * hcount.full;
            assert s' == point_view_index(bi, 2*j + 1, hsize);

            var w := x_value(2 * j, hcount);
            var vo := modadd(a[s], modmul(a[s'], w));
            var ve := modsub(a[s], modmul(a[s'], w));

            var hpoints := level_points_view(a, hsize);
            var hpoints' := level_points_view(a', hsize);
            var size := hsize.full;

            forall i | (0 <= i < bi || bi + 1 <= i < hcount.full)
                ensures hpoints[i] == hpoints'[i];
                ensures 0 <= i < bi ==> points_eval_prefix_inv(hpoints'[i], higher[bit_rev_int(i, hcount)], 2*j+2, hcount);
                ensures bi + 1 <= i < hcount.full ==> points_eval_prefix_inv(hpoints'[i], higher[bit_rev_int(i, hcount)], 2*j, hcount);
            {
                var left := hpoints[i];
                var right := hpoints'[i];
    
                assert left == right by {
                    forall k | 0 <= k < hsize.full 
                        ensures a[point_view_index(i, k, hsize)]
                            == a'[point_view_index(i, k, hsize)];
                    {
                        point_view_index_disjont_lemma(i, k, bi, 2*j, hsize);
                        point_view_index_disjont_lemma(i, k, bi, 2*j+1, hsize);
                    }
                }
            }

            var left := hpoints[bi];
            var right := hpoints'[bi];
            var poly := higher[bit_rev_int(bi, hcount)];

            assert points_eval_prefix_inv(right, poly, 2*j+2, hcount) by {
                reveal points_eval_prefix_inv();
                forall k | 0 <= k < 2*j+2 
                    ensures poly_eval(poly, x_value(k, hcount)) == right[k];
                {
                    if k != 2*j && k != 2*j+1 {
                        point_view_index_disjont_lemma(bi, k, bi, 2*j, hsize);
                        point_view_index_disjont_lemma(bi, k, bi, 2*j+1, hsize);
                        assert right[k] == left[k];
                    } else {
                        ct_butterfly_even_lemma(a, hcount, j, bi, s, w);
                        ct_butterfly_odd_lemma(a, hcount, j, bi, s, w);
                    }
                }
            }
        }

        // lemma s_loop_perserves_inv_lemma(a: n_sized, a': n_sized, hcount: pow2_t, j: nat, bi: nat)
        //     requires s_loop_inv(a, hcount, j, bi);
        //     requires s_loop_update(a, a', hcount, j, bi);
        // {
            

        // }
    }
}