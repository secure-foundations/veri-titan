include "nth_root.dfy"

abstract module ct_std2rev_model {
    import opened Seq
	import opened Power
	import opened Power2
	import opened DivMod
	import opened Mul

	import opened pows_of_2
    import opened ntt_index
    import opened nth_root
    import opened ntt_512_params
	import opened mq_polys
    import opened poly_view

    ghost const x_value: x_fun

    predicate {:opaque} t_loop_inv(a: n_sized, count: pow2_t, coefficients: n_sized)
        requires 0 <= count.exp <= N.exp;
    {
        var sz := block_size(count);
        var points := level_points_view(a, sz);
        var polys := level_polys(coefficients, sz);
        forall i | 0 <= i < count.full ::
            points_eval_inv(points[i], polys[bit_rev_int(i, count)], x_value, count)
    }

    lemma t_loop_inv_pre_specialized_lemma(points: seq<elem>, poly: seq<elem>, A_i: elem)
        requires poly == [A_i];
        requires points == [A_i];
        ensures points_eval_inv(points, poly, x_value, N)
    {
        assert points_eval_inv(points, poly, x_value, N) by
        {
            reveal points_eval_suffix_inv();
            assert N.exp <= N.exp;
            poly_eval_base_lemma(poly, x_value(0, N));
            assert points[0] == poly_eval(poly, x_value(0, N));
        }
    }

    lemma t_loop_inv_pre_lemma(coefficients: n_sized)
        ensures N.exp <= N.exp; // ??
        ensures t_loop_inv(coefficients, N, coefficients);
    {
        reveal t_loop_inv();
        assert N.exp <= N.exp; // ??
        var sz := block_size(N);
        assert sz.full == 1;
        assert sz.exp == 0;
        var lpoints := level_points_view(coefficients, sz);
        var lpolys := base_level_polys(coefficients);

        forall i | 0 <= i < N.full
            ensures points_eval_inv(lpoints[i],
                lpolys[bit_rev_int(i, N)], x_value, N)
        {
            base_level_polys_lemma(coefficients, i);
            var points := lpoints[i];
            var poly := lpolys[bit_rev_int(i, N)];
            assert poly == [coefficients[i]];
            t_loop_inv_pre_specialized_lemma(points, poly, coefficients[i]);
        }
    }

    predicate ntt_eval_all(a: n_sized, coefficients: n_sized)
    {
        points_eval_inv(a, coefficients, x_value, pow2(0))
    }

    lemma t_loop_inv_post_lemma(a: n_sized, one: pow2_t, coefficients: n_sized)
        requires one.exp == 0 <= N.exp;
        requires t_loop_inv(a, one, coefficients);
        ensures ntt_eval_all(a, coefficients);
    {
        reveal t_loop_inv();
        var sz := block_size(one);
        var points := level_points_view(a, sz);
        var polys := level_polys(coefficients, sz);
        Nth_root_lemma();
        pow2_basics(one);
        assert one.full == 1;
        assert sz == N;
        assert points[0] == a;

        assert polys[0] == coefficients by {
            reveal level_polys();
        }
    }

    datatype loop_view = loop_view(
        coefficients: n_sized,
        lower: seq<seq<elem>>, // lower polys
        higher: seq<seq<elem>>, // higher polys
        hsize: pow2_t)
    {
        predicate loop_view_wf()
        {
            && 1 <= hsize.exp <= N.exp
            && unifromly_sized(higher, hsize)
		    && higher == level_polys(coefficients, hsize)
		    && lower == level_polys(coefficients, pow2_half(hsize))
        }

        function lsize(): (r: pow2_t)
            requires loop_view_wf();
            ensures r.full <= N.full;
        {
            var r := pow2_half(hsize);
            assert r.full <= N.full by {
                reveal Pow2();
                LemmaPowIncreases(2, r.exp, N.exp);
            }
            r
        }

        function lcount(): (r: pow2_t)
            requires loop_view_wf();
        {
            block_count(lsize())
        }

        function hcount(): (r: pow2_t)
            requires loop_view_wf();
            ensures r.full <= N.full;
        {
            var r := block_count(hsize);
            assert r.full <= N.full by {
                reveal Pow2();
                LemmaPowIncreases(2, r.exp, N.exp);
            }
            r            
        }

        lemma size_count_lemma()
            requires loop_view_wf();
            ensures pow2_double(lsize()) == hsize;
            ensures lcount() == pow2_double(hcount());
            ensures lcount().full * lsize().full
                == hcount().full * hsize.full == N.full;
        {
            Nth_root_lemma();
            block_count_half_lemma(hsize);
        }

        // lemma size_count_bound_lemma()
        //     requires loop_view_wf();
        //     ensures lsize().full <= N.full;
        //     ensures hsize.full <= N.full;
        // {
        //     reveal Pow2();
        //     LemmaPowIncreases(2, hsize.exp, N.exp);
        // }


        // static function init_loop_view(): (v: loop_view) 
        //     ensures v.loop_view_wf();
        // {   
        //     var hsize := pow2(1);
        //     loop_view(
        //         level_polys(pow2_half(hsize)), 
        //         level_polys(hsize),
        //         hsize)
        // }

        predicate {:opaque} j_loop_higher_inv(a: n_sized, hcount: pow2_t, j: nat)
            requires hcount.exp <= N.exp;
            requires loop_view_wf();
            requires hsize == block_size(hcount);
        {
            && var hpoints := level_points_view(a, hsize);
            && (forall i | 0 <= i < hcount.full ::
                points_eval_prefix_inv(hpoints[i], higher[bit_rev_int(i, hcount)], x_value, 2*j, hcount))
        }

        predicate {:opaque} j_loop_lower_inv(a: n_sized, hcount: pow2_t, j: nat)
            requires hcount.exp <= N.exp;
            requires loop_view_wf();
            requires hsize == block_size(hcount);
        {
            && var lcount := lcount();
            && var lpoints := level_points_view(a, lsize());
            && (forall i | 0 <= i < lcount.full ::
                points_eval_suffix_inv(lpoints[i], lower[bit_rev_int(i, lcount)], x_value, j, lcount))
        }

        predicate j_loop_inv(a: n_sized, hcount: pow2_t, j: nat)
        {
            && loop_view_wf()
            && hcount.exp <= N.exp
            && hsize == block_size(hcount)
            && j <= lsize().full
            && j_loop_higher_inv(a, hcount, j)
            && j_loop_lower_inv(a, hcount, j)
        }

        predicate {:opaque} s_loop_higher_inv(a: n_sized, hcount: pow2_t, j: nat, bi: nat)
            requires hcount.exp <= N.exp;
            requires bi <= hcount.full;
            requires loop_view_wf();
            requires hsize == block_size(hcount);
        {
            && var hpoints := level_points_view(a, hsize);
            && (forall i | 0 <= i < bi ::
                points_eval_prefix_inv(hpoints[i], higher[bit_rev_int(i, hcount)], x_value, 2*j+2, hcount))
            && (forall i | bi <= i < hcount.full ::
                points_eval_prefix_inv(hpoints[i], higher[bit_rev_int(i, hcount)], x_value, 2*j, hcount))
        }

        predicate {:opaque} s_loop_lower_inv(a: n_sized, hcount: pow2_t, j: nat, bi: nat)
            requires hcount.exp <= N.exp;
            requires bi <= hcount.full;
            requires loop_view_wf();
            requires hsize == block_size(hcount);
        {
            size_count_lemma();
            && var lcount := lcount();
            && var lpoints := level_points_view(a, lsize());
            && (forall i | (0 <= i < bi || hcount.full <= i < bi + hcount.full) ::
                && (points_eval_suffix_inv(lpoints[i], lower[bit_rev_int(i, lcount)], x_value, j+1, lcount)))
            && (forall i | (bi <= i < hcount.full || bi + hcount.full <= i < lcount.full) ::
                points_eval_suffix_inv(lpoints[i], lower[bit_rev_int(i, lcount)], x_value, j, lcount))
        }

        predicate s_loop_inv(a: n_sized, hcount: pow2_t, j: nat, bi: nat)
        {
            && loop_view_wf()
            && hcount.exp <= N.exp
            && bi <= hcount.full
            && j < lsize().full
            && hsize == block_size(hcount)
            && s_loop_higher_inv(a, hcount, j, bi)
            && s_loop_lower_inv(a, hcount, j, bi)
        }

        // lemma s_loop_index_bound(a: n_sized, hcount: pow2_t, j: nat, bi: nat)
        //     requires loop_view_wf();
        //     requires hcount.exp <= N.exp;
        //     requires bi < hcount.full;
        //     requires j < lsize().full;
        //     requires hsize == block_size(hcount);
        //     ensures bi + (2*j) * hcount.full + hcount.full < N.full;
        //     ensures bi + hcount.full < lcount().full;
        // {
        //     size_count_lemma();
        //     point_view_index_bound_lemma(bi, 2 * j+1, hsize);
        //     LemmaMulIsDistributive(hcount.full, 2*j, 1);
        //     assert (2*j) * hcount.full + hcount.full == (2*j + 1) * hcount.full;
        // }

        lemma higher_points_view_index_lemma(a: n_sized, hcount: pow2_t, j: nat, bi: nat)
            returns (s: nat)
    
            requires s_loop_inv(a, hcount, j, bi);
            requires bi < hcount.full
            ensures s == bi + (2*j) * hcount.full;
            ensures s + hcount.full < N.full;
            ensures a[s] == level_points_view(a, hsize)[bi][2*j];
            ensures s == point_view_index(bi, 2*j, hsize);
            ensures a[s+hcount.full] == level_points_view(a, hsize)[bi][2*j+1];
            ensures s+hcount.full == point_view_index(bi, 2*j+1, hsize);
        {
            size_count_lemma();
            var hpoints := level_points_view(a, hsize);
            LemmaMulNonnegative(2*j, hcount.full);
            s := bi + (2*j) * hcount.full;

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

        lemma lower_points_view_index_lemma(a: n_sized, hcount: pow2_t, j: nat, bi: nat)
            returns (s: nat)

            requires s_loop_inv(a, hcount, j, bi);
            requires bi < hcount.full
            ensures s == bi + (2*j) * hcount.full;
            ensures s + hcount.full < N.full;
            ensures bi + hcount.full < lcount().full;
            ensures a[s] == level_points_view(a, lsize())[bi][j];
            ensures s == point_view_index(bi, j, lsize());
            ensures a[s+hcount.full] == level_points_view(a, lsize())[bi+hcount.full][j];
            ensures s+hcount.full == point_view_index(bi+hcount.full, j, lsize());
        {
            size_count_lemma();
            var lpoints := level_points_view(a, lsize());
            LemmaMulNonnegative(2*j, hcount.full);
            s := bi + (2*j) * hcount.full;

            calc == {
                s;
                bi + (2*j) * hcount.full;
                {
                    LemmaMulProperties();
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
            requires loop_view_wf();
            requires bi < lcount().full;
        {
            lower[bit_rev_int(bi, lcount())]
        }

        function get_odd_poly(bi: nat): seq<elem>
            requires loop_view_wf();
            requires bi + hcount().full < lcount().full;
        {
            lower[bit_rev_int(bi+hcount().full, lcount())]
        }

        function get_full_poly(bi: nat): seq<elem>
            requires loop_view_wf();
            requires bi < hcount().full;
        {
            higher[bit_rev_int(bi, hcount())]
        }
    
        lemma lower_points_view_value_lemma(a: n_sized, hcount: pow2_t, j: nat, bi: nat, s: nat)
            requires s_loop_inv(a, hcount, j, bi);
            requires bi < hcount.full;
            requires s == bi + (2*j) * hcount.full;
            ensures s + hcount.full < N.full;
            ensures bi + hcount.full < lcount().full;
            ensures a[s] == poly_eval(get_even_poly(bi), x_value(j, lcount()));
            ensures a[s+hcount.full] == poly_eval(get_odd_poly(bi), x_value(j, lcount()));
        {
            size_count_lemma();
            var _ := lower_points_view_index_lemma(a, hcount, j, bi);
            var lpoints := level_points_view(a, lsize());
            var lcount := lcount();

            var e_poly := get_even_poly(bi);
            var e_points := lpoints[bi];

            assert a[s] == poly_eval(e_poly, x_value(j, lcount)) by {
                assert points_eval_suffix_inv(e_points, e_poly, x_value, j, lcount) by {
                    reveal s_loop_lower_inv();
                }
                reveal points_eval_suffix_inv();
                assert a[s] == e_points[j];
            }

            var o_poly := get_odd_poly(bi);
            var o_points := lpoints[bi+hcount.full];

            assert a[s+hcount.full] == poly_eval(o_poly, x_value(j, lcount)) by {
                assert points_eval_suffix_inv(o_points, o_poly, x_value, j, lcount) by {
                    reveal s_loop_lower_inv();
                }
                reveal points_eval_suffix_inv();
                assert a[s+hcount.full] == lpoints[bi+hcount.full][j];
            }
        }

        lemma level_polys_bitrev_index_correspondence_lemma(a: n_sized, hcount: pow2_t, j: nat, bi: nat)
            requires s_loop_inv(a, hcount, j, bi);
            requires bi < hcount.full
            ensures |get_full_poly(bi)| == hsize.full;
            ensures bi + hcount.full < lcount().full;
            ensures get_even_poly(bi) == even_indexed_items(get_full_poly(bi), hsize);
            ensures get_odd_poly(bi) == odd_indexed_items(get_full_poly(bi), hsize);
        {
            size_count_lemma();

            var ri := bit_rev_int(bi, hcount);
            var poly := higher[ri];

            level_polys_index_correspondence_lemma(coefficients, higher, hsize, ri, lower);

            assert even_indexed_items(poly, hsize) == lower[2 * ri];
            assert odd_indexed_items(poly, hsize) == lower[2 * ri + 1];

            bit_rev_int_lemma0(bi, hcount);
            bit_rev_int_lemma1(bi, hcount);
            // assert bit_rev_int(bi, lcount()) == 2 * ri;
            // assert bit_rev_int(bi + hcount.full, lcount()) == 2 * ri + 1;
        }

        predicate s_loop_update(a: n_sized, a': n_sized, hcount: pow2_t, j: nat, bi: nat)
            requires s_loop_inv(a, hcount, j, bi);
            requires x_value.requires(2*j, hcount);
            requires bi < hcount.full
        {
            var s := bi + (2*j) * hcount.full;
            var w := mqmul(x_value(2 * j, hcount), R);
            point_view_index_bound_lemma(bi, 2 * j+1, hsize);
            point_view_index_bound_lemma(bi, 2 * j, hsize);
            LemmaMulIsDistributive(hcount.full, 2*j, 1);
            assert (2*j) * hcount.full + hcount.full == (2*j + 1) * hcount.full;
            var s' := s+hcount.full; 
            a' == a[s := mqadd(a[s], montmul(a[s'], w))]
                [s' := mqsub(a[s], montmul(a[s'], w))]
        }

        lemma s_loop_perserves_higher_inv_lemma(a: n_sized, a': n_sized, hcount: pow2_t, j: nat, bi: nat)
            requires s_loop_inv(a, hcount, j, bi);
            requires x_value.requires(2*j, hcount);
            requires bi < hcount.full
            requires s_loop_update(a, a', hcount, j, bi);
            ensures s_loop_higher_inv(a', hcount, j, bi+1);
        {
            reveal s_loop_higher_inv();

            var s := higher_points_view_index_lemma(a, hcount, j, bi);
            var s' := s+hcount.full;
            assert s == point_view_index(bi, 2*j, hsize);
            assert s' == point_view_index(bi, 2*j + 1, hsize);

            // var vo := mqadd(a[s], mqmul(a[s'], w));
            // var ve := mqsub(a[s], mqmul(a[s'], w));

            var hpoints := level_points_view(a, hsize);
            var hpoints' := level_points_view(a', hsize);
            var size := hsize.full;

            forall i | (0 <= i < bi || bi + 1 <= i < hcount.full)
                ensures hpoints[i] == hpoints'[i];
                ensures 0 <= i < bi ==> points_eval_prefix_inv(hpoints'[i], higher[bit_rev_int(i, hcount)], x_value, 2*j+2, hcount);
                ensures bi + 1 <= i < hcount.full ==> points_eval_prefix_inv(hpoints'[i], higher[bit_rev_int(i, hcount)], x_value, 2*j, hcount);
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

            assert points_eval_prefix_inv(right, poly, x_value, 2*j+2, hcount) by {
                reveal points_eval_prefix_inv();
                forall k | 0 <= k < 2*j+2 
                    ensures poly_eval(poly, x_value(k, hcount)) == right[k];
                {
                    if k != 2*j && k != 2*j+1 {
                        point_view_index_disjont_lemma(bi, k, bi, 2*j, hsize);
                        point_view_index_disjont_lemma(bi, k, bi, 2*j+1, hsize);
                        assert right[k] == left[k];
                    } else {
                        var w := mqmul(x_value(2 * j, hcount), R);
                        ct_butterfly_even_lemma(this, a, hcount, j, bi, s, w);
                        ct_butterfly_odd_lemma(this, a, hcount, j, bi, s, w);
                    }
                }
            }
        }

        lemma s_loop_perserves_lower_inv_lemma(a: n_sized, a': n_sized, hcount: pow2_t, j: nat, bi: nat)
            requires s_loop_inv(a, hcount, j, bi);
            requires bi < hcount.full
            requires s_loop_update(a, a', hcount, j, bi);
            ensures s_loop_lower_inv(a', hcount, j, bi+1);
        {
            size_count_lemma();
            var s := lower_points_view_index_lemma(a, hcount, j, bi);
            var s' := s+hcount.full;
            assert s == point_view_index(bi, j, lsize());
            assert s+hcount.full == point_view_index(bi+hcount.full, j, lsize());

            reveal s_loop_lower_inv();

            var lpoints := level_points_view(a, lsize());
            var lpoints' := level_points_view(a', lsize());
            var lsize := lsize();
            var count := lcount();

            forall i | (bi + 1 <= i < hcount.full || bi + hcount.full + 1 <= i < count.full) 
                ensures points_eval_suffix_inv(lpoints'[i], lower[bit_rev_int(i, count)], x_value, j, count);
            {
                var left := lpoints[i];
                var right := lpoints'[i];
    
                assert left == right by {
                    forall k | 0 <= k < lsize.full 
                        ensures a[point_view_index(i, k, lsize)]
                            == a'[point_view_index(i, k, lsize)];
                    {
                        point_view_index_disjont_lemma(i, k, bi, j, lsize);
                        point_view_index_disjont_lemma(i, k, bi + hcount.full, j, lsize);
                    }
                }
            }
        
            forall i | (0 <= i <= bi || hcount.full <= i <= bi + hcount.full)
                ensures points_eval_suffix_inv(lpoints'[i], lower[bit_rev_int(i, count)], x_value, j+1, count);
            {
                var left := lpoints[i];
                var right := lpoints'[i];
                var poly := lower[bit_rev_int(i, count)];

                if i == bi || i == bi + hcount.full {
                    assert points_eval_suffix_inv(right, poly, x_value, j+1, count) by {
                        reveal points_eval_suffix_inv();
                        forall k | j + 1 <= k < lsize.full
                            ensures right[k] == left[k];
                            ensures poly_eval(poly, x_value(k, count)) == right[k];
                        {
                            // assert left[k] == a[point_view_index(bi, k, lsize)];
                            // assert right[k] == a'[point_view_index(bi, k, lsize)];

                            point_view_index_disjont_lemma(bi, k, bi, j, lsize);
                            point_view_index_disjont_lemma(bi, k, bi + hcount.full, j, lsize);
                            point_view_index_disjont_lemma(bi + hcount.full, k, bi, j, lsize);
                            point_view_index_disjont_lemma(bi + hcount.full, k, bi + hcount.full, j, lsize);

                            assert right[k] == left[k];
                        }
                    }
                } else {
                    assert left == right by {
                        forall k | 0 <= k < lsize.full 
                            ensures a[point_view_index(i, k, lsize)]
                                == a'[point_view_index(i, k, lsize)];
                        {
                            point_view_index_disjont_lemma(i, k, bi, j, lsize);
                            point_view_index_disjont_lemma(i, k, bi + hcount.full, j, lsize);
                        }
                    }
                }
            }
        }

        lemma s_loop_inv_peri_lemma(a: n_sized, a': n_sized, hcount: pow2_t, j: nat, bi: nat)
            requires s_loop_inv(a, hcount, j, bi);
            requires bi < hcount.full
            requires s_loop_update(a, a', hcount, j, bi);
            ensures s_loop_inv(a', hcount, j, bi+1);
        {
            s_loop_perserves_higher_inv_lemma(a, a', hcount, j, bi);
            s_loop_perserves_lower_inv_lemma(a, a', hcount, j, bi);
        }

        lemma s_loop_inv_pre_lemma(a: n_sized, hcount: pow2_t, j: nat)
            requires j_loop_inv(a, hcount, j);
            requires j < lsize().full;
            ensures s_loop_inv(a, hcount, j, 0);
        {
            assert s_loop_higher_inv(a, hcount, j, 0) by {
                reveal s_loop_higher_inv();
                reveal j_loop_higher_inv();
            }

            size_count_lemma();
    
            assert s_loop_lower_inv(a, hcount, j, 0) by {
                reveal s_loop_lower_inv();
                reveal j_loop_lower_inv();

                var lcount := lcount();
                var lpoints := level_points_view(a, lsize());

                forall i | (0 <= i < hcount.full || hcount.full <= i < lcount.full)
                    ensures points_eval_suffix_inv(lpoints[i], lower[bit_rev_int(i, lcount)], x_value, j, lcount);
                {
                    assert (0 <= i < hcount.full || hcount.full <= i < lcount.full)
                        ==> (0 <= i < lcount.full);
                }
            }
        }

        lemma s_loop_inv_post_lemma(a: n_sized, hcount: pow2_t, j: nat, bi: nat)
            requires s_loop_inv(a, hcount, j, bi);
            requires bi == hcount.full;
            ensures j_loop_inv(a, hcount, j + 1)
        {
            assert j_loop_higher_inv(a, hcount, j+1) by {
                var hpoints := level_points_view(a, hsize);
                reveal s_loop_higher_inv();
                forall i | 0 <= i < |hpoints|
                    ensures points_eval_prefix_inv(hpoints[i], higher[bit_rev_int(i, hcount)], x_value, 2*j+2, hcount);
                {
                }
                reveal j_loop_higher_inv();
            }

            size_count_lemma();

            assert j_loop_lower_inv(a, hcount, j+1) by {
                var lcount := lcount();
                var lpoints := level_points_view(a, lsize());
                reveal s_loop_lower_inv();
                forall i | 0 <= i < |lpoints|
                    ensures points_eval_suffix_inv(lpoints[i], lower[bit_rev_int(i, lcount)], x_value, j+1, lcount);
                {
                }
                reveal j_loop_lower_inv();
            }
        }

        lemma j_loop_inv_pre_lemma(a: n_sized, hcount: pow2_t)
            requires 0 <= hcount.exp < N.exp;
            requires t_loop_inv(a, pow2_double(hcount), coefficients);
            requires loop_view_wf();
            requires hsize == block_size(hcount);
            ensures j_loop_inv(a, hcount, 0);
        {
            assert j_loop_higher_inv(a, hcount, 0) by {
                var hpoints := level_points_view(a, hsize);
                forall i | 0 <= i < hcount.full
                    ensures points_eval_prefix_inv(hpoints[i], higher[bit_rev_int(i, hcount)], x_value, 0, hcount);
                {
                    unifromly_sized_instance_lemma(hpoints, hsize, i);
                    unifromly_sized_instance_lemma(higher, hsize, bit_rev_int(i, hcount));
                    points_eval_prefix_inv_vacuous_lemma(hpoints[i], higher[bit_rev_int(i, hcount)], x_value, hcount);
                }
                reveal j_loop_higher_inv();
            }
    
            assert pow2_double(hcount) == lcount();

            assert j_loop_lower_inv(a, hcount, 0) by {
                reveal t_loop_inv();
                var lcount := lcount();
                var lpoints := level_points_view(a, lsize());
                forall i | 0 <= i < lcount.full
                    ensures points_eval_suffix_inv(lpoints[i], lower[bit_rev_int(i, lcount)], x_value, 0, lcount)
                {
                    reveal points_eval_suffix_inv();
                }
                reveal j_loop_lower_inv();
            }
        }

        lemma j_loop_inv_post_lemma(a: n_sized, hcount: pow2_t, j: nat)
            requires j_loop_inv(a, hcount, j);
            requires j == lsize().full;
            requires 0 <= hsize.exp <= N.exp;
            requires hsize == block_size(hcount);
            ensures t_loop_inv(a, hcount, coefficients);
        {
            reveal j_loop_higher_inv();
            size_count_lemma();
            var hpoints := level_points_view(a, hsize);

            forall i | 0 <= i < hcount.full
                ensures points_eval_inv(hpoints[i], higher[bit_rev_int(i, hcount)], x_value, hcount);
            {
                reveal points_eval_suffix_inv();
                reveal points_eval_prefix_inv();
            }

            assert t_loop_inv(a, hcount, coefficients) by {
                reveal t_loop_inv();
            }
        }
    }

    function build_loop_view(coefficients: n_sized, hcount: pow2_t): (view: loop_view)
        requires 0 <= hcount.exp < N.exp
        ensures view.loop_view_wf();
    {
        var hsize := block_size(hcount);
        loop_view(
            coefficients,
            level_polys(coefficients, pow2_half(hsize)),
            level_polys(coefficients, hsize),
            hsize)
    }

    lemma x_value_odd_square_lemma(view: loop_view, j: nat, x: elem)
        requires view.loop_view_wf();
        requires 2 * j < view.hsize.full;
        requires x == x_value(2 * j + 1, view.hcount());
        ensures mqmul(x, x) == x_value(j, view.lcount());

    lemma x_value_even_square_lemma(view: loop_view, j: nat, x: elem)
        requires view.loop_view_wf();
        requires 2 * j < view.hsize.full;
        requires x == x_value(2 * j, view.hcount());
        ensures mqmul(x, x) == x_value(j, view.lcount());

    lemma ct_butterfly_even_lemma(view: loop_view, a: n_sized, hcount: pow2_t, j: nat, bi: nat, s: nat, w: elem)
        requires view.s_loop_inv(a, hcount, j, bi);
        requires s == bi + (2*j) * hcount.full;
        requires bi < hcount.full
        requires w == mqmul(x_value(2 * j, hcount), R);
        ensures s + hcount.full < N.full;
        ensures bi + hcount.full < view.lcount().full;
        ensures poly_eval(view.get_full_poly(bi), x_value(2*j, hcount))
            == mqadd(a[s], montmul(a[s+hcount.full], w));

    lemma ct_butterfly_odd_lemma(view: loop_view, a: n_sized, hcount: pow2_t, j: nat, bi: nat, s: nat, w: elem)
        requires view.s_loop_inv(a, hcount, j, bi);
        requires bi < hcount.full
        requires s == bi + (2*j) * hcount.full;
        requires w == mqmul(x_value(2 * j, hcount), R);
        ensures s + hcount.full < N.full;
        ensures bi + hcount.full < view.lcount().full;
        ensures poly_eval(view.get_full_poly(bi), x_value(2*j+1, hcount))
            == mqsub(a[s], montmul(a[s+hcount.full], w));
}

module forward_ntt refines ct_std2rev_model {

    ghost const x_value := rev_mixed_powers_mont_x_value;

    lemma x_value_even_square_lemma(view: loop_view, j: nat, x: elem)
        // requires loop_view_wf();
        // requires 2 * j < view.hsize.full;
        // requires x == x_value(2 * j, view.hcount());
        // ensures mqmul(x, x) == x_value(j, view.lcount());
    {
        view.size_count_lemma();
        var hc := view.hcount();
        var hsize := view.hsize;
        var lsize := view.lsize();
        var lcount := view.lcount();

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
            2 * (2 * bit_rev_int(2 * j , hsize) * hc.full) + lcount.full;
            {
                LemmaMulIsCommutative(2, bit_rev_int(2 * j , hsize));
            }
            2 * (bit_rev_int(2 * j , hsize) * 2 * hc.full) + lcount.full;
            {
                LemmaMulIsAssociative(bit_rev_int(2 * j , hsize), 2, hc.full);
            }
            2 * (bit_rev_int(2 * j , hsize) * (2 * hc.full)) + lcount.full;
            2 * (bit_rev_int(2 * j , hsize) * lcount.full) + lcount.full;
            {
                LemmaMulIsAssociative(2, bit_rev_int(2 * j , hsize), lcount.full);
            }
            2 * bit_rev_int(2 * j , hsize) * lcount.full + lcount.full;
            {
                bit_rev_int_lemma2(j, lsize);
            }
            2 * bit_rev_int(j , lsize) * lcount.full + lcount.full;
        }

        var temp := Pow(PSI, exp);

        calc == {
            mqmul(x, x);
            ((temp % Q) * (temp % Q)) % Q;
            {
                LemmaMulModNoopGeneral(temp, temp, Q);
            }
            (temp * temp) % Q;
            {
                LemmaPowAdds(PSI, exp, exp);
            }
            Pow(PSI, 2 * exp) % Q;
            x_value(j, lcount);
        }
    }

    lemma x_value_odd_square_lemma(view: loop_view, j: nat, x: elem)
        // requires view.loop_view_wf();
        // requires 2 * j < view.hsize.full;
        // requires x_value.requires(2 * j + 1, view.hcount());
        // requires x == x_value(2 * j + 1, view.hcount());
        // ensures mqmul(x, x) == x_value(j, view.lcount());
    {
        view.size_count_lemma();
        var hc := view.hcount();
        var hsize := view.hsize;
        var lsize := view.lsize();
        var lcount := view.lcount();

        LemmaMulNonnegative(bit_rev_int(2 * j + 1, hsize), hc.full);
        LemmaMulIsAssociative(2, bit_rev_int(2 * j + 1, hsize), hc.full);
        var exp := 2 * bit_rev_int(2 * j + 1, hsize) * hc.full + hc.full;   

        var temp := Pow(PSI, exp);

        calc == {
            2 * exp;
            2 * (2 * bit_rev_int(2 * j + 1, hsize) * hc.full + hc.full);
            {
                LemmaMulIsDistributive(2, 2 * bit_rev_int(2 * j + 1, hsize) * hc.full, hc.full);
            }
            2 * (2 * bit_rev_int(2 * j + 1, hsize) * hc.full) + 2 * hc.full;
            2 * (2 * bit_rev_int(2 * j + 1, hsize) * hc.full) + lcount.full;
            {
                LemmaMulIsCommutative(2, bit_rev_int(2 * j + 1, hsize));
            }
            2 * (bit_rev_int(2 * j + 1, hsize) * 2 * hc.full) + lcount.full;
            {
                LemmaMulIsAssociative(bit_rev_int(2 * j + 1, hsize), 2, hc.full);
            }
            2 * (bit_rev_int(2 * j + 1, hsize) * (2 * hc.full)) + lcount.full;
            2 * (bit_rev_int(2 * j + 1, hsize) * lcount.full) + lcount.full;
            {
                LemmaMulIsAssociative(2, bit_rev_int(2 * j + 1, hsize), lcount.full);
            }
            2 * bit_rev_int(2 * j + 1, hsize) * lcount.full + lcount.full;
            {
                bit_rev_int_lemma3(j, lsize);
            }
            2 * (bit_rev_int(j, lsize) + lsize.full) * lcount.full + lcount.full;
            {
                LemmaMulIsAssociative(2, bit_rev_int(j, lsize) + lsize.full, lcount.full);
            }
            2 * ((bit_rev_int(j, lsize) + lsize.full) * lcount.full) + lcount.full;
            {
                LemmaMulIsDistributive(lcount.full, bit_rev_int(j, lsize), lsize.full);
            }
            2 * (bit_rev_int(j, lsize) * lcount.full + lsize.full * lcount.full) + lcount.full;
            {
                view.size_count_lemma();
                LemmaMulIsCommutative(lsize.full, lcount.full);
                assert lsize.full * lcount.full == N.full;
            }
            2 * (bit_rev_int(j, lsize) * lcount.full + N.full) + lcount.full;
            {
                LemmaMulIsDistributive(2, bit_rev_int(j, lsize) * lcount.full, N.full);
            }
            2 * (bit_rev_int(j, lsize) * lcount.full) + 2 * N.full + lcount.full;
            {
                LemmaMulIsAssociativeAuto();
            }
            2 * bit_rev_int(j, lsize) * lcount.full + 2 * N.full + lcount.full;
        }

        calc == {
            mqmul(x, x);
            ((temp % Q) * (temp % Q)) % Q;
            {
                LemmaMulModNoopGeneral(temp, temp, Q);
            }
            (temp * temp) % Q;
            {
                LemmaPowAdds(PSI, exp, exp);
            }
            Pow(PSI, 2 * exp) % Q;
            Pow(PSI, 2 * bit_rev_int(j, lsize) * lcount.full + 2 * N.full + lcount.full) % Q;
            {
                LemmaMulNonnegative(2 * bit_rev_int(j, lsize), lcount.full);
                full_rotation_lemma(2 * bit_rev_int(j, lsize) * lcount.full + lcount.full);
            }
            Pow(PSI, 2 * bit_rev_int(j, lsize) * lcount.full + lcount.full) % Q;
        }
    }

    lemma ct_butterfly_even_lemma(view: loop_view, a: n_sized, hcount: pow2_t, j: nat, bi: nat, s: nat, w: elem)
        // requires view.s_loop_inv(a, hcount, j, bi);
        // requires s == bi + (2*j) * hcount.full;
        // requires bi < hcount.full
        // requires w == mqmul(x_value(2 * j, hcount), R);
        // ensures s + hcount.full < N.full;
        // ensures bi + hcount.full < view.lcount().full;
        // ensures poly_eval(view.get_full_poly(bi), x_value(2*j, hcount))
        //     == mqadd(a[s], montmul(a[s+hcount.full], w));
    {
        view.size_count_lemma();
        view.lower_points_view_value_lemma(a, hcount, j, bi, s);
        var e := a[s];
        var o := a[s+hcount.full];
        var p := montmul(o, w);

        gbassert IsModEquivalent(p, o * x_value(2 * j, hcount), Q) by {
            assert IsModEquivalent(p, o * w * R_INV, Q) by {
                LemmaSmallMod(p, Q);
            }
            assert IsModEquivalent(R_INV * R, 1, Q) by {
                Nth_root_lemma();
            }
            assert IsModEquivalent(w, x_value(2 * j, hcount) * R, Q) by {
                LemmaSmallMod(w, Q);
            }
        }

        assert p == (o * x_value(2 * j, hcount)) % Q by {
            LemmaSmallMod(p, Q);
        }

        var sum := mqadd(e, p);
        var diff := mqsub(e, p);

        var e_poly := view.get_even_poly(bi);
        var o_poly := view.get_odd_poly(bi);
        var f_poly := view.get_full_poly(bi);

        view.level_polys_bitrev_index_correspondence_lemma(a, hcount, j, bi);

        var x := x_value(2*j, hcount);
        var sqr := x_value(j, view.lcount());

        assert e == poly_eval(e_poly, sqr);
        assert o == poly_eval(o_poly, sqr);

        x_value_even_square_lemma(view, j, x);

        poly_eval_split_lemma(f_poly, e_poly, o_poly, view.hsize, x);
    }


    lemma ct_butterfly_odd_lemma(view: loop_view, a: n_sized, hcount: pow2_t, j: nat, bi: nat, s: nat, w: elem)
        // requires view.s_loop_inv(a, hcount, j, bi);
        // requires bi < hcount.full
        // requires s == bi + (2*j) * hcount.full;
        // requires w == mqmul(x_value(2 * j, hcount), R);
        // ensures s + hcount.full < N.full;
        // ensures bi + hcount.full < view.lcount().full;
        // ensures poly_eval(view.get_full_poly(bi), x_value(2*j+1, hcount))
        //     == mqsub(a[s], montmul(a[s+hcount.full], w));
    {
        view.size_count_lemma();
        view.lower_points_view_value_lemma(a, hcount, j, bi, s);
        var e := a[s];
        var o := a[s+hcount.full];
        var p := montmul(o, w);

        var hsize := view.hsize;
        var lsize := view.lsize();
        var lcount := view.lcount();

        gbassert IsModEquivalent(p, o * x_value(2*j, hcount), Q) by {
            assert IsModEquivalent(p, o * w * R_INV, Q) by {
                LemmaSmallMod(p, Q);
            }
            assert IsModEquivalent(R_INV * R, 1, Q) by {
                Nth_root_lemma();
            }
            assert IsModEquivalent(w, x_value(2*j, hcount) * R, Q) by {
                LemmaSmallMod(w, Q);
            }
        }

        assert p == (o * x_value(2 * j, hcount)) % Q by {
            LemmaSmallMod(p, Q);
        }

        var diff := mqsub(e, p);

        var e_poly := view.get_even_poly(bi);
        var o_poly := view.get_odd_poly(bi);
        var f_poly := view.get_full_poly(bi);

        var x_e := x_value(2*j, hcount);
        var x_o := x_value(2*j+1, hcount);
    
        x_value_odd_square_lemma(view, j, x_o);

        view.level_polys_bitrev_index_correspondence_lemma(a, hcount, j, bi);

        var sqr := x_value(j, lcount);

        calc == {
            x_o;
            {
                LemmaMulNonnegative(2 * bit_rev_int(2*j+1, hsize), hcount.full);
            }
            mqpow(PSI, 2 * bit_rev_int(2*j+1, hsize) * hcount.full + hcount.full);
            {
                bit_rev_int_lemma3(j, lsize);
                assert bit_rev_int(2*j+1, hsize) == bit_rev_int(j, lsize) + lsize.full;
            }
            mqpow(PSI, 2 * (bit_rev_int(j, lsize) + lsize.full) * hcount.full + hcount.full);
            {
                gbassert 2 * (bit_rev_int(j, lsize) + lsize.full) * hcount.full == 2 * (bit_rev_int(j, lsize) * hcount.full) + N.full by {
                    assert 2 * lsize.full * hcount.full == N.full;
                }
            }
            mqpow(PSI, 2 * (bit_rev_int(j, lsize) * hcount.full) + N.full + hcount.full);
            {
                LemmaMulNonnegative(bit_rev_int(j, lsize), hcount.full);
                half_rotation_lemma(2 * (bit_rev_int(j, lsize) * hcount.full) + hcount.full);
            }
            (Q - mqpow(PSI, 2 * (bit_rev_int(j, lsize) * hcount.full) + hcount.full)) % Q;
            {
                LemmaMulIsAssociative(2, bit_rev_int(j, lsize), hcount.full);
            }
            (Q - mqpow(PSI, 2 * bit_rev_int(j, lsize) * hcount.full + hcount.full)) % Q;
            {
                bit_rev_int_lemma2(j, lsize);
            }
            (Q - mqpow(PSI, 2 * bit_rev_int(2*j, hsize) * hcount.full + hcount.full)) % Q;
            (Q - x_e) % Q;
            {
                LemmaSmallMod(Q- x_e, Q);
            }
            Q - x_e;
        }

        calc == {
            diff;
            mqsub(e, mqmul(o, x_e));
            {
                LemmaMulNonnegative(o, x_e);
            }
            (e as int - ((o * x_e) % Q)) % Q;
            {
                LemmaSubModNoopRight(e, o * x_e, Q);
            }
            (e as int - (o * x_e)) % Q;
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
            {
                LemmaSmallMod(e, Q);
            }
            (e + (x_o * o) % Q) % Q;
            (e + mqmul(x_o, o)) % Q;
            mqadd(e, mqmul(x_o, o));
            mqadd(poly_eval(e_poly, sqr), mqmul(x_o, poly_eval(o_poly, sqr)));
            {
                poly_eval_split_lemma(f_poly, e_poly, o_poly, view.hsize, x_o);
            }
            poly_eval(f_poly, x_o);
        }
    }
}

module inverse_ntt refines ct_std2rev_model {

    ghost const x_value := rev_omega_inv_powers_x_value;

    lemma x_value_even_square_lemma(view: loop_view, j: nat, x: elem)
        // requires loop_view_wf();
        // requires 2 * j < view.hsize.full;
        // requires x == x_value(2 * j, view.hcount());
        // ensures mqmul(x, x) == x_value(j, view.lcount());
    {
        view.size_count_lemma();

        var hc := view.hcount();
        var hsize := view.hsize;
        var lsize := view.lsize();
        var lcount := view.lcount();

        LemmaMulNonnegative(bit_rev_int(2 * j, hsize), hc.full);
        LemmaMulIsAssociative(2, bit_rev_int(2 * j, hsize), hc.full);
        var exp := bit_rev_int(2 * j , hsize) * hc.full;

        assert x == mqpow(OMEGA_INV, exp);

        calc == {
            2 * exp;
            2 * (bit_rev_int(2 * j , hsize) * hc.full);
            {
                bit_rev_int_lemma2(j, lsize);
            }
            2 * (bit_rev_int(j, lsize) * hc.full);
            {
                LemmaMulProperties();
            }
            bit_rev_int(j, lsize) * (2 * hc.full);
            bit_rev_int(j, lsize) * lcount.full;
        }

        var temp := Pow(OMEGA_INV, exp);

        calc == {
            mqmul(x, x);
            ((temp % Q) * (temp % Q)) % Q;
            {
                LemmaMulModNoopGeneral(temp, temp, Q);
            }
            (temp * temp) % Q;
            {
                LemmaPowAdds(OMEGA_INV, exp, exp);
                assert exp + exp == 2 * exp;
            }
            Pow(OMEGA_INV, 2 * exp) % Q;
            x_value(j, lcount);
        }
    }

    lemma x_value_odd_square_lemma(view: loop_view, j: nat, x: elem)
        // requires loop_view_wf();
        // requires 2 * j < hsize.full;
        // requires x == x_value(2 * j + 1, hcount());
        // ensures mqmul(x, x) == x_value(j, lcount());
    {
        view.size_count_lemma();

        var hc := view.hcount();
        var hsize := view.hsize;
        var lsize := view.lsize();
        var lcount := view.lcount();

        LemmaMulNonnegative(bit_rev_int(2 * j + 1, hsize), hc.full);
        LemmaMulIsAssociative(2, bit_rev_int(2 * j + 1, hsize), hc.full);
        var exp := bit_rev_int(2 * j + 1, hsize) * hc.full;   
        assert x == mqpow(OMEGA_INV, exp);
        var temp := Pow(OMEGA_INV, exp);

        calc == {
            2 * exp;
            2 * (bit_rev_int(2 * j + 1, hsize) * hc.full);
            {
                LemmaMulProperties();
            }
            (2 * bit_rev_int(2 * j + 1, hsize)) * hc.full;
            {
                bit_rev_int_lemma3(j, lsize);
            }
            (2 * (bit_rev_int(j, lsize) + lsize.full)) * hc.full;
            {
                LemmaMulIsDistributive(2, bit_rev_int(j, lsize), lsize.full);
            }
            (2 * bit_rev_int(j, lsize) + 2 * lsize.full) * hc.full;
            {
                LemmaMulIsDistributive(hc.full, 2 * bit_rev_int(j, lsize), 2 * lsize.full);
            }
            2 * bit_rev_int(j, lsize) * hc.full + 2 * lsize.full * hc.full;
            2 * bit_rev_int(j, lsize) * hc.full + N.full;
            {
                LemmaMulProperties();
            }
            bit_rev_int(j, lsize) * (2 * hc.full) + N.full;
            bit_rev_int(j, lsize) * lcount.full + N.full;
        }

        calc == {
            mqmul(x, x);
            ((temp % Q) * (temp % Q)) % Q;
            {
                LemmaMulModNoopGeneral(temp, temp, Q);
            }
            (temp * temp) % Q;
            {
                LemmaPowAdds(OMEGA_INV, exp, exp);
            }
            Pow(OMEGA_INV, 2 * exp) % Q;
            Pow(OMEGA_INV, bit_rev_int(j, lsize) * lcount.full + N.full) % Q;
            {
                LemmaMulNonnegative(bit_rev_int(j, lsize), lcount.full);
                inv_full_rotation_lemma(bit_rev_int(j, lsize) * lcount.full);
            }
            Pow(OMEGA_INV, bit_rev_int(j, lsize) * lcount.full) % Q;
        }
    }

    lemma ct_butterfly_even_lemma(view: loop_view, a: n_sized, hcount: pow2_t, j: nat, bi: nat, s: nat, w: elem)
        // requires s_loop_inv(a, hcount, j, bi);
        // requires s == bi + (2*j) * hcount.full;
        // requires bi < hcount.full
        // requires w == mqmul(x_value(2 * j, hcount), R);
        // ensures s + hcount.full < N.full;
        // ensures bi + hcount.full < lcount().full;
        // ensures poly_eval(get_full_poly(bi), x_value(2*j, hcount)) == mqadd(a[s], montmul(a[s+hcount.full], w));
    {
        view.size_count_lemma();
        view.lower_points_view_value_lemma(a, hcount, j, bi, s);
        var e := a[s];
        var o := a[s+hcount.full];
        var p := montmul(o, w);

        gbassert IsModEquivalent(p, o * x_value(2 * j, hcount), Q) by {
            assert IsModEquivalent(p, o * w * R_INV, Q) by {
                LemmaSmallMod(p, Q);
            }
            assert IsModEquivalent(R_INV * R, 1, Q) by {
                Nth_root_lemma();
            }
            assert IsModEquivalent(w, x_value(2 * j, hcount) * R, Q) by {
                LemmaSmallMod(w, Q);
            }
        }

        assert p == (o * x_value(2 * j, hcount)) % Q by {
            LemmaSmallMod(p, Q);
        }

        var sum := mqadd(e, p);
        var diff := mqsub(e, p);

        var e_poly := view.get_even_poly(bi);
        var o_poly := view.get_odd_poly(bi);
        var f_poly := view.get_full_poly(bi);

        view.level_polys_bitrev_index_correspondence_lemma(a, hcount, j, bi);

        var x := x_value(2*j, hcount);
        var sqr := x_value(j, view.lcount());

        assert e == poly_eval(e_poly, sqr);
        assert o == poly_eval(o_poly, sqr);

        x_value_even_square_lemma(view, j, x);

        poly_eval_split_lemma(f_poly, e_poly, o_poly, view.hsize, x);
    }

    lemma ct_butterfly_odd_lemma(view: loop_view, a: n_sized, hcount: pow2_t, j: nat, bi: nat, s: nat, w: elem)
        // requires s_loop_inv(a, hcount, j, bi);
        // requires bi < hcount.full
        // requires s == bi + (2*j) * hcount.full;
        // requires w == mqmul(x_value(2 * j, hcount), R);
        // ensures s + hcount.full < N.full;
        // ensures bi + hcount.full < lcount().full;
        // ensures poly_eval(get_full_poly(bi), x_value(2*j+1, hcount))
        //     == mqsub(a[s], montmul(a[s+hcount.full], w));
    {
        view.size_count_lemma();

        var hc := view.hcount();
        var hsize := view.hsize;
        var lsize := view.lsize();
        var lcount := view.lcount();
    
        view.lower_points_view_value_lemma(a, hcount, j, bi, s);
        var e := a[s];
        var o := a[s+hcount.full];
        var p := montmul(o, w);

        gbassert IsModEquivalent(p, o * x_value(2*j, hcount), Q) by {
            assert IsModEquivalent(p, o * w * R_INV, Q) by {
                LemmaSmallMod(p, Q);
            }
            assert IsModEquivalent(R_INV * R, 1, Q) by {
                Nth_root_lemma();
            }
            assert IsModEquivalent(w, x_value(2*j, hcount) * R, Q) by {
                LemmaSmallMod(w, Q);
            }
        }

        assert p == (o * x_value(2 * j, hcount)) % Q by {
            LemmaSmallMod(p, Q);
        }

        var diff := mqsub(e, p);

        var e_poly := view.get_even_poly(bi);
        var o_poly := view.get_odd_poly(bi);
        var f_poly := view.get_full_poly(bi);

        var x_e := x_value(2*j, hcount);
        var x_o := x_value(2*j+1, hcount);
    
        x_value_odd_square_lemma(view, j, x_o);

        view.level_polys_bitrev_index_correspondence_lemma(a, hcount, j, bi);

        var sqr := x_value(j, lcount);

        calc == {
            x_o;
            {
                LemmaMulNonnegative(bit_rev_int(2*j+1, hsize), hcount.full);
            }
            mqpow(OMEGA_INV, bit_rev_int(2*j+1, hsize) * hcount.full);
            {
                bit_rev_int_lemma3(j, lsize);
                assert bit_rev_int(2*j+1, hsize) == bit_rev_int(j, lsize) + lsize.full;
            }
            mqpow(OMEGA_INV, (bit_rev_int(j, lsize) + lsize.full) * hcount.full);
            {
                LemmaMulIsDistributive(hcount.full, bit_rev_int(j, lsize), lsize.full);
            }
            mqpow(OMEGA_INV, bit_rev_int(j, lsize) * hcount.full + lsize.full * hcount.full);
            {
                bit_rev_int_lemma2(j, lsize);
            }
            mqpow(OMEGA_INV, bit_rev_int(2 * j, hsize) * hcount.full + lsize.full * hcount.full);
            {
                LemmaMulNonnegative(bit_rev_int(2 * j, hsize), hcount.full);
                inv_half_rotation_lemma(bit_rev_int(2 * j, hsize) * hcount.full);
                assert lsize.full * hcount.full == N.full / 2 by {
                    LemmaMulProperties();
                }
            }
            (Q - x_e) % Q;
            {
                LemmaSmallMod(Q - x_e, Q);
            }
            Q - x_e;
        }

        calc == {
            diff;
            mqsub(e, mqmul(o, x_e));
            {
                LemmaMulNonnegative(o, x_e);
            }
            (e as int - ((o * x_e) % Q)) % Q;
            {
                LemmaSubModNoopRight(e, o * x_e, Q);
            }
            (e as int - (o * x_e)) % Q;
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
            {
                LemmaSmallMod(e, Q);
            }
            (e + (x_o * o) % Q) % Q;
            (e + mqmul(x_o, o)) % Q;
            mqadd(e, mqmul(x_o, o));
            mqadd(poly_eval(e_poly, sqr), mqmul(x_o, poly_eval(o_poly, sqr)));
            {
                poly_eval_split_lemma(f_poly, e_poly, o_poly, hsize, x_o);
            }
            poly_eval(f_poly, x_o);
        }
    }
}