include "ntt_rec.dfy"

module ntt {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul

    import opened pows_of_2
    import opened omegas
    import opened ntt_recs
    import opened rindex
    import opened bins
    import opened polys

    type n_sized = s: seq<elem>
        | |s| == N == pow2(L).full witness *

    lemma chunk_index_bounded(len: pow2_t, ki: nat)
        requires 0 <= len.exp <= L;
        requires ki <= chunk_count(len);
        ensures ki < chunk_count(len) ==> 0 <= ki * len.full <= N - len.full;
        ensures ki == chunk_count(len) ==> 0 <= ki * len.full == N;
    {
        nth_root_lemma();
        if ki == chunk_count(len) {
            return;
        }
        var max_count := chunk_count(len);
        var csize := len.full;
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

    lemma y_as_chunks_prefix_lemma(y: n_sized, y': n_sized, len: pow2_t, i: nat)
        requires 0 <= len.exp <= L;
        requires i <= chunk_count(len);
        requires 0 <= i * len.full <= N;
        requires y[..i * len.full] == y'[..i * len.full];
        ensures y_as_chunks(y, len)[..i] == y_as_chunks(y', len)[..i];
    {
        var csize := len.full;
        var v1 := y_as_chunks(y, len)[..i];
        var v2 := y_as_chunks(y', len)[..i];

        forall ki: nat | 0 <= ki < i
            ensures v1[ki] == v2[ki];
        {
            chunk_index_bounded(len, ki);

            var lo := ki * csize;
            var hi := ki * csize + csize;

            assert hi <= i * len.full by {
                LemmaMulInequality(ki, i-1, len.full);
                LemmaMulIsCommutativeAuto();
                LemmaMulIsDistributiveSubAuto();
            }

            assert y[..hi] == y'[..hi];
            assert y[lo..hi] == y'[lo..hi];
        }
    }

    lemma y_as_chunks_suffix_lemma(y: n_sized, y': n_sized, len: pow2_t, i: nat)
        requires 0 <= len.exp <= L;
        requires i <= chunk_count(len);
        requires 0 <= i * len.full <= N;
        requires y[i * len.full..] == y'[i * len.full..];
        ensures y_as_chunks(y, len)[i..] == y_as_chunks(y', len)[i..];
    {
        var count := chunk_count(len) - i;
        var csize := len.full;
        var v1 := y_as_chunks(y, len)[i..];
        var v2 := y_as_chunks(y', len)[i..];

        forall ki: nat | 0 <= ki < count
            ensures v1[ki] == v2[ki];
        {
            chunk_index_bounded(len, ki + i);

            var lo := (ki + i) * csize;
            var hi := lo + csize;

            assert i * len.full <= lo by {
                assert i <= ki + i;
                LemmaMulInequality(i, i+ki, len.full);
            }

            assert y[lo..] == y'[lo..];
            assert y[lo..hi] == y'[lo..hi];
        }
    }

    datatype chunk_loop_view = chunk_loop_view(
        lower: level_view,
        higher: level_view)
    {
        predicate ntt_loop_views_wf()
        {
            && N == pow2(L).full
            && 2 <= higher.m.full <= N
            && 1 <= higher.m.exp <= L
            && lower.m == pow2_half(higher.m)
            && higher.valid_level_view()
            && lower == higher.build_lower_level()
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

        function hi_coeffs(ki: nat): seq<elem>
            requires ntt_loop_views_wf();
            requires ki < chunk_count(higher.m);
        {
            higher.a[hi_idx(ki)]
        }

        lemma index_bounded_lemma(ki: nat, j: nat)
            requires ntt_loop_views_wf();
            requires ki < chunk_count(higher.m);
            requires 0 <= j <= lower.m.full;
            ensures j != lower.m.full ==>
                0 <= ki * higher.m.full + j + lower.m.full < N;
            ensures j == lower.m.full ==>
                0 <= ki * higher.m.full + j + lower.m.full <= N;
        {
            var len := higher.m.full;
            chunk_index_bounded(higher.m, ki);
            // assert 0 <= ki * len <= N - len;
        }

        predicate ntt_level_loop_inv(y: n_sized, ki: nat)
        {
            && ntt_loop_views_wf()
            && ki <= chunk_count(higher.m)
            && |y| == N == pow2(L).full
            && y_as_chunks(y, lower.m)[lo_idx(ki)..]
                == lower.ntt_rec()[lo_idx(ki)..]
            && y_as_chunks(y, higher.m)[..hi_idx(ki)]
                == higher.ntt_rec()[..hi_idx(ki)]
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

        lemma lower_view_points_lemma(y: n_sized, ki: nat)
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
            var vy := lower.ntt_rec();

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
            assert even_chunk == read_chunk(y, len', kl) == vy[kl];
            assert odd_chunk == read_chunk(y, len', kl + 1) == vy[kl + 1];

            assert poly_eval_all_points(lower.a[lo_idx(ki)], read_even_chunk(y, ki), lower.m);
            assert poly_eval_all_points(lower.a[lo_idx(ki)+1], read_odd_chunk(y, ki), lower.m);
        }

        lemma lower_view_point_lemma(y: n_sized, ki: nat, j: nat)
            requires ntt_level_loop_inv(y, ki);
            requires ki < chunk_count(higher.m);
            requires j < lower.m.full;
            ensures lo_idx(ki) < |lower.a| - 1;
            ensures y[start_point(ki)+j]
                == poly_eval(lower.a[lo_idx(ki)], omega_nk(lower.m, j));
            ensures y[split_point(ki)+j]
                == poly_eval(lower.a[lo_idx(ki)+1], omega_nk(lower.m, j));
        {
            lower_view_points_lemma(y, ki);
            var kl := lo_idx(ki);
            var a_e := lower.a[kl];
            var a_o := lower.a[kl + 1];
            var even_chunk := read_even_chunk(y, ki);
            var odd_chunk := read_odd_chunk(y, ki);

            assert even_chunk[j] == y[start_point(ki)+j] by {
                SubsequenceIndex(y, start_point(ki), split_point(ki), j);
            }

            assert odd_chunk[j] == y[split_point(ki)+j] by {
                SubsequenceIndex(y, split_point(ki), end_point(ki), j);
            }

            assert even_chunk[j] == poly_eval(a_e, omega_nk(lower.m, j)) by {
                poly_eval_all_points_lemma(a_e, even_chunk, lower.m, j);
            }

            assert odd_chunk[j] == poly_eval(a_o, omega_nk(lower.m, j)) by {
                poly_eval_all_points_lemma(a_o, odd_chunk, lower.m, j);
            }
        }

        predicate poly_eval_first_half(y: elem, ki: nat, i: nat)
            requires ntt_loop_views_wf();
            requires ki < chunk_count(higher.m);
        {
            y == poly_eval(hi_coeffs(ki), omega_nk(higher.m, i))
        }

        predicate poly_eval_second_half(y: elem, ki: nat, i: nat)
            requires ntt_loop_views_wf();
            requires ki < chunk_count(higher.m);
        {
            y == poly_eval(hi_coeffs(ki), omega_nk(higher.m, i+lower.m.full))
        }

        predicate {:opaque} poly_eval_halves(y': n_sized, ki: nat, j: nat)
            requires ntt_loop_views_wf();
            requires ki < chunk_count(higher.m);
            requires j <= lower.m.full;
        {
            var a := start_point(ki);
            var b := split_point(ki);
            forall i | 0 <= i < j :: (
                && poly_eval_first_half(y'[a+i], ki, i) 
                && poly_eval_second_half(y'[b+i], ki, i))
        }

        predicate ntt_chunk_loop_inv(y: n_sized, y': n_sized,
            omg: elem, ki: nat, j: nat)
        {
            && ntt_level_loop_inv(y, ki)
            && j <= lower.m.full
            && omg == modpow(omega_n(higher.m), j)
            && ki < chunk_count(higher.m)
            && var a := start_point(ki);
            && var b := split_point(ki);
            && var c := end_point(ki);
            && |y'| == |y|
            && y'[..a] == y[..a]
            && y'[c..] == y[c..]
            && y'[a+j..b] == y[a+j..b] == read_even_chunk(y, ki)[j..]
            && y'[b+j..c] == y[b+j..c] == read_odd_chunk(y, ki)[j..]
            && poly_eval_halves(y', ki, j)
        }

        // this is pretty stupid
        lemma ntt_chunk_loop_post_point_specialized_lemma(y: n_sized, y': n_sized,
            omg: elem, ki: nat, i: nat)
            requires ntt_loop_views_wf();
            requires 0 <= i < lower.m.full;
            requires ki < chunk_count(higher.m);
            requires poly_eval_halves(y', ki, lower.m.full);
            ensures poly_eval_first_half(y'[start_point(ki)+i], ki, i);
            ensures poly_eval_second_half(y'[split_point(ki)+i], ki, i);
        {
            reveal poly_eval_halves();
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

            reveal poly_eval_halves();
        }

        lemma chunk_loop_peri_point_lemma(y: n_sized, y1: n_sized,
            omg: elem, t: elem, u: elem,
            ki: nat, j: nat)
            requires ntt_chunk_loop_inv(y, y1, omg, ki, j);
            requires j < lower.m.full;
            requires t == modmul(omg, y[split_point(ki) + j]);
            requires u == y[start_point(ki) + j];
            ensures poly_eval_first_half(modadd(u, t), ki, j);
            ensures poly_eval_second_half(modsub(u, t), ki, j);
        {
            lower_view_point_lemma(y, ki, j);

            var y_e_k := y[start_point(ki)+j];
            var y_o_k := y[split_point(ki)+j];
            assert y_e_k == poly_eval(lower.a[lo_idx(ki)], omega_nk(lower.m, j));
            assert y_o_k == poly_eval(lower.a[lo_idx(ki)+1], omega_nk(lower.m, j));

            assert lower.a[lo_idx(ki)] == even_indexed_terms(hi_coeffs(ki), higher.m) by {
                higher.ntt_level_terms_correspondence_lemma(lower, ki);
            }
            assert lower.a[lo_idx(ki)+1] == odd_indexed_terms(hi_coeffs(ki), higher.m) by {
                higher.ntt_level_terms_correspondence_lemma(lower, ki);
            }

            y_k_value_lemma(hi_coeffs(ki), lower.m, higher.m, 
                omg, j, y_e_k, y_o_k, modadd(u, t));

            y_k'_value_lemma(hi_coeffs(ki), lower.m, higher.m, 
                omg, j, y_e_k, y_o_k, modsub(u, t));
        }

        lemma chunk_loop_peri_lemma(y: n_sized,
            y1: n_sized, y2: n_sized,
            omg: elem, t: elem, u: elem,
            ki: nat, j: nat)
            requires ntt_chunk_loop_inv(y, y1, omg, ki, j);
            requires j < lower.m.full;
            requires t == modmul(omg, y[split_point(ki) + j]);
            requires u == y[start_point(ki) + j];
            requires y2 == y1[start_point(ki) + j := modadd(u, t)]
                [split_point(ki) + j := modsub(u, t)];
            ensures ntt_chunk_loop_inv(y, y2, modmul(omg, omega_n(higher.m)), ki, j+1);
        {
            var a := start_point(ki);
            var b := split_point(ki);
            var c := end_point(ki);
            var omgm := omega_n(higher.m);

            calc == {
                y2[a+j+1..b];
                y1[a+j+1..b];
                y[a+j+1..b];
                read_even_chunk(y, ki)[j+1..];
            }

            calc == {
                y2[b+j+1..c];
                y1[b+j+1..c];
                y[b+j+1..c];
                read_odd_chunk(y, ki)[j+1..];
            }

            assert poly_eval_halves(y2, ki, j+1) by {
                reveal poly_eval_halves();
                forall i | 0 <= i < j+1
                    ensures poly_eval_first_half(y2[a+i], ki, i);
                    ensures poly_eval_second_half(y2[b+i], ki, i);
                {
                    if i != j {
                        assert y2[a+i] == y1[a+i];
                        assert y2[b+i] == y1[b+i];
                    } else {
                        assert y2[a+i] == modadd(u, t);
                        assert y2[b+i] == modsub(u, t);
                        chunk_loop_peri_point_lemma(y, y1, omg, t, u, ki, j);
                    }
                }
            }

            omg_inv_lemma(omgm, omg, higher.m, j);
        }

        lemma chunk_loop_post_points_lemma(y: n_sized, y': n_sized, omg: elem, ki: nat)
            requires ntt_chunk_loop_inv(y, y', omg, ki, lower.m.full);
            // ensures poly_eval_all_points(hi_coeffs(ki), y'[start_point(ki)..end_point(ki)], higher.m);
            ensures higher.ntt_rec()[hi_idx(ki)] == y'[start_point(ki)..end_point(ki)];
        {
            var a := start_point(ki);
            var b := split_point(ki);
            var c := end_point(ki);
            hi_lo_idx_relations(ki);

            forall i: nat | 0 <= i < higher.m.full
                ensures y'[a..c][i] == poly_eval(hi_coeffs(ki), omega_nk(higher.m, i));
            {
                assert y'[a+i] == y'[a..c][i];
                if i < lower.m.full {
                    ntt_chunk_loop_post_point_specialized_lemma(y, y', omg, ki, i);
                } else {
                    var l := i - lower.m.full;
                    ntt_chunk_loop_post_point_specialized_lemma(y, y', omg, ki, l);
                }
            }

            assert poly_eval_all_points(hi_coeffs(ki), y'[a..c], higher.m) by {
                reveal poly_eval_all_points();
            }

            assert poly_eval_all_points(hi_coeffs(ki), higher.ntt_rec()[hi_idx(ki)], higher.m);

            assert higher.ntt_rec()[hi_idx(ki)] == y'[a..c] by {
                reveal poly_eval_all_points();
            }
        }

        lemma chunk_loop_post_lemma(y: n_sized, y': n_sized, omg: elem, ki: nat)
            requires ntt_chunk_loop_inv(y, y', omg, ki, lower.m.full);
            ensures ntt_level_loop_inv(y', ki+1);
        {
            var old_y_lo := y_as_chunks(y, lower.m);
            var new_y_lo := y_as_chunks(y', lower.m);

            var old_y_hi := y_as_chunks(y, higher.m);
            var new_y_hi := y_as_chunks(y', higher.m);

            var lo_view := lower.ntt_rec();
            var hi_view := higher.ntt_rec();
    
            hi_lo_idx_relations(ki);

            chunk_index_bounded(lower.m, lo_idx(ki+1));

            assert y[lo_idx(ki+1)*lower.m.full..] == y'[lo_idx(ki+1)*lower.m.full..] by {
                calc {
                    end_point(ki);
                    lo_idx(ki) * lower.m.full + higher.m.full;
                    lo_idx(ki) * lower.m.full + 2 * lower.m.full;
                    {
                        LemmaMulIsDistributiveAddOtherWay(lower.m.full, lo_idx(ki), 2);
                    }
                    (lo_idx(ki) + 2) * lower.m.full;
                    lo_idx(ki+1)*lower.m.full;
                }
            }

            calc == {
                new_y_lo[lo_idx(ki+1)..];
                {
                    y_as_chunks_suffix_lemma(y, y', lower.m, lo_idx(ki+1));
                    assert new_y_lo[lo_idx(ki+1)..] == old_y_lo[lo_idx(ki+1)..];
                }
                old_y_lo[lo_idx(ki+1)..];
                lo_view[lo_idx(ki+1)..];
            }

            var new_chunk := y'[start_point(ki)..end_point(ki)];

            calc == {
                new_y_hi[..hi_idx(ki+1)];
                new_y_hi[..hi_idx(ki)] + [new_y_hi[hi_idx(ki)]];
                new_y_hi[..hi_idx(ki)] + [new_chunk];
                {
                    y_as_chunks_prefix_lemma(y, y', higher.m, hi_idx(ki));
                    assert old_y_hi[..hi_idx(ki)] == new_y_hi[..hi_idx(ki)];
                }
                old_y_hi[..hi_idx(ki)] + [new_chunk];
                {
                    assert old_y_hi[..hi_idx(ki)] == hi_view[..hi_idx(ki)];
                }
                hi_view[..hi_idx(ki)] + [new_chunk];
                {
                    chunk_loop_post_points_lemma(y, y', omg, ki);
                }
                hi_view[..hi_idx(ki)] + [higher.ntt_rec()[hi_idx(ki)]];
            }
        }
    }

    datatype lvl_loop_view = lvl_loop_view(lvls: seq<level_view>)
    {
        predicate lvl_loop_views_wf()
        {
            && |lvls| == L + 1
            && (forall i| 0 <= i <= L :: lvls[i].m == pow2(i))
            && (forall i| 0 <= i < L ::
                chunk_loop_view(lvls[i], lvls[i+1]).ntt_loop_views_wf())
        }

        function method get_chunk_loop_view(s: nat): (cv: chunk_loop_view)
            requires 1 <= s <= L;
            requires lvl_loop_views_wf();
            ensures cv.ntt_loop_views_wf();
            ensures cv.higher.m == pow2(s);
        {
            chunk_loop_view(lvls[s-1], lvls[s])
        }

        predicate lvl_loop_views_inv(y: n_sized, s: nat)
        {
            && 1 <= s <= L + 1
            && lvl_loop_views_wf()
            && (1 <= s <= L ==> get_chunk_loop_view(s).ntt_level_loop_inv(y, 0))
            && (s == L + 1 ==> poly_eval_all_points(A(), y, pow2(L)))
        }

       lemma level_loop_post_special_lemma(y: n_sized, y': n_sized, s: nat)
            requires lvl_loop_views_inv(y, s);
            requires s == L;
            requires get_chunk_loop_view(s).ntt_level_loop_inv(y', chunk_count(pow2(s)));
            ensures poly_eval_all_points(A(), y', pow2(s));
        {
            var c_view := get_chunk_loop_view(s);
            var m := pow2(s);
            nth_root_lemma();
            assert m.full == N;
            
            calc == {
                y';
                y_as_chunks(y', m)[0];
                c_view.higher.ntt_rec()[0];
            }

            assert poly_eval_all_points(c_view.higher.a[0], y', m);
            assert c_view.higher.a[0] == A();
        }

        lemma level_loop_post_lemma(y: n_sized, y': n_sized, s: nat)
            requires lvl_loop_views_inv(y, s);
            requires 1 <= s <= L;
            requires get_chunk_loop_view(s).ntt_level_loop_inv(y', chunk_count(pow2(s)));
            ensures 1 <= s <= L ==> lvl_loop_views_inv(y', s+1);
        {
            if s == L {
                level_loop_post_special_lemma(y, y', s);
                return;
            }

            var c_view := get_chunk_loop_view(s);
            var c_view' := get_chunk_loop_view(s+1);
    
            var m := pow2(s);
            var count := chunk_count(m);
            c_view.hi_lo_idx_relations(count);

            calc == {
                y_as_chunks(y', m);
                c_view.higher.ntt_rec();
                lvls[s].ntt_rec();
                c_view'.lower.ntt_rec();
            }

            assert c_view'.higher.ntt_rec()[..0]
                == y_as_chunks(y', c_view'.higher.m)[..0];

            assert c_view'.ntt_level_loop_inv(y', 0);
        }
    }

    method ntt_chunk_loop(
        y: n_sized, 
        k: nat,
        ki: nat,
        view: chunk_loop_view)
    returns (y': n_sized)
        requires view.ntt_level_loop_inv(y, ki);
        requires ki < chunk_count(view.higher.m);
        requires k == view.hi_idx(ki) * view.higher.m.full;
        ensures view.ntt_level_loop_inv(y', ki+1);
    {
        y' := y;
        var len' := view.lower.m;
        var omgm := omega_n(view.higher.m);

        var omg := 1;
        var j := 0;

        pow2_basics(view.higher.m);

        view.index_bounded_lemma(ki, 0);
        view.hi_lo_idx_relations(ki);
        view.chunk_loop_pre_lemma(y, ki);

        while (j < len'.full)
            invariant |y'| == |y|;
            invariant view.ntt_chunk_loop_inv(y, y', omg, ki, j);
        {
            var y1 := y';
            view.index_bounded_lemma(ki, j);

            var t := modmul(omg, y[k + j + len'.full]);
            var u := y[k + j];
            y' := y'[k + j := modadd(u, t)];
            y' := y'[k + j + len'.full := modsub(u, t)];

            view.chunk_loop_peri_lemma(y, y1, y', omg, t, u, ki, j);
            omg := modmul(omg, omgm);
            j := j + 1;
        }

        view.chunk_loop_post_lemma(y, y', omg, ki);
    }

    method ntt_level_loop(y: n_sized, s: nat, l_view: lvl_loop_view)
    returns (y': n_sized)
        requires l_view.lvl_loop_views_inv(y, s);
        requires 1 <= s <= L;
        ensures l_view.lvl_loop_views_inv(y', s + 1);
    {
        y' := y;
        var c_view := l_view.get_chunk_loop_view(s);
        var m := pow2(s);
        assert m == c_view.higher.m;
        pow2_basics(m);

        var k := 0;
        var ki := 0;

        while (ki < chunk_count(m)) 
            invariant c_view.ntt_level_loop_inv(y', ki);
            invariant 0 <= k == ki * m.full;
        {
            var k' := k + m.full;
            var ki' := ki + 1;

            y' := ntt_chunk_loop(y', k, ki, c_view);

            assert k' == (ki + 1) * m.full by {
                LemmaMulIsDistributiveAddOtherWay(m.full, ki, 1);
                assert (ki + 1) * m.full == ki * m.full + 1 * m.full;
            }
            assert (ki + 1) * m.full > 0 by {
                LemmaMulStrictlyPositiveAuto();
            }
            k, ki := k', ki';
        }

        l_view.level_loop_post_lemma(y, y', s);
    }

    method ntt(y: n_sized, l_view: lvl_loop_view) returns (y': n_sized)
        requires l_view.lvl_loop_views_inv(y, 1);
        ensures poly_eval_all_points(A(), y', pow2(L));
    {
        y' := y;
        var s := 1;
        while (s <= L)
            invariant l_view.lvl_loop_views_inv(y', s);
            invariant 1 <= s;
        {
            y' := ntt_level_loop(y', s, l_view);
            s := s + 1;
        }
    }
}