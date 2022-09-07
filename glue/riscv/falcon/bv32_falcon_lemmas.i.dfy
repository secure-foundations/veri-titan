include "../../generic_falcon_lemmas.dfy"
include "mq_arith_lemmas.dfy"

module bv32_falcon_lemmas refines generic_falcon_lemmas {
    import opened Seq
    import opened Power2
    import opened DivModNeg
    import opened rv_machine
    import opened rv_vale
    import opened mem
    import flat
    import opened bv32_op_s

    import opened mq_arith_lemmas

    predicate fvar_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(iter, heap, if address >= 0 then address else iter.cur_ptr())
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && contains_elems(iter.buff)
    }

    lemma forward_s_loop_inv_pre_lemma(
        a: seq<nat>,
        d: pow2_t,
        j: nat,
        t: pow2_t,
        u: nat,
        ot3: uint32,
        t3: uint32,
        t6: uint32,
        s5: uint32,
        view: FNTT.loop_view)

        requires forward_j_loop_inv(a, d, j, u, view);
        requires t == view.lsize();
        requires j < view.lsize().full;
        requires t.full < BASE_32;
        requires s5 == uint32_ls(uint32_add(t.full, j), 1);
        requires t6 == 2 * d.full;
        requires ot3 == 2 * u;
        requires t3 == uint32_add(ot3, t6);

        ensures forward_s_loop_inv(a, d, j, 0, view);
        ensures s5 == (t.full + j) * 2; 
        ensures t.full + j < N.full;
        ensures t3 == 2 * u + 2 * d.full;
        ensures |FNTT.rev_mixed_powers_mont_table()| == N.full;
        ensures FNTT.rev_mixed_powers_mont_table()[t.full + j] == 
            MQP.mqmul(FNTT.rev_mixed_powers_mont_x_value(2 * j, d), R);
    {
        view.s_loop_inv_pre_lemma(as_elems(a), d, j);
        FNTT.rev_mixed_powers_mont_table_lemma(t, d, j);
        assert uint32_add(t.full, j) == t.full + j;
        ls1_is_double(t.full + j);
        FNTT.rev_mixed_powers_mont_table_lemma(t, d, j);

        assert u == j * (2 * d.full);
        assert d == view.hcount();

        calc {
            j * (2 * d.full) + d.full;
            <= 
            {
                LemmaMulInequality(j, 512, 2 * d.full);
            }
            512 * (2 * d.full) + d.full;
        }
        assert FNTT.N == N;
        assert FNTT.Q == Q;
        assert FNTT.R == R;
    }

    lemma forward_s_loop_inv_post_lemma(
        a: seq<nat>,
        d: pow2_t,
        j: nat,
        u: uint32,
        bi: nat,
        ot3: uint32,
        t3: uint32,
        t6: uint32,
        view: FNTT.loop_view)
    
        requires bi == d.full;
        requires t6 == 2 * d.full;
        requires u == j * (2 * d.full);
        requires forward_s_loop_inv(a, d, j, bi, view);
        requires ot3 == 2 * u + 2 * d.full;
        requires t3 == uint32_add(ot3, t6);
        ensures t3 == 2 * (u + 2 * d.full);
        ensures forward_j_loop_inv(a, d, j + 1, u + 2 * d.full, view);
    {
        view.s_loop_inv_post_lemma(as_elems(a), d, j, bi);

        assert u + 2 * d.full == (j + 1) * (2 * d.full) by {
            LemmaMulProperties();
        }

        calc == {
            ot3 + t6;
            2 * u + 2 * d.full + 2 * d.full;
            2 * (j * (2 * d.full)) + 2 * d.full + 2 * d.full;
            {
                LemmaMulProperties();
            }
            (2 * j + 2) * (2 * d.full);
        }

        assert d == view.hcount();

        calc {
            (2 * j + 2) * (2 * d.full);
            <= 
            {
                LemmaMulInequality(2 * j + 2, 1024, 2 * d.full);
            }
            1024 * (2 * d.full);
            <
            {
                assert d.full <= 512;
            }
            BASE_31;
        }
    }

    lemma forward_s_loop_index_lemma(
        a: seq<nat>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s4: uint32,
        s2: uint32,
        t4: uint32,
        t5: uint32,
        t6: uint32,
        view: FNTT.loop_view)
        returns (s: nat)

        requires forward_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        requires s2 == 2 * bi + 2 * (j * (2 * d.full)); 
        requires flat.ptr_admissible_32(heap_b32_index_ptr(s4, N.full / 2 - 1));
        requires t4 == uint32_add(s4, s2);
        requires t5 == uint32_add(t4, t6);
        requires t6 == 2 * d.full;

        ensures s == bi + (2*j) * d.full;
        ensures t4 == s4 + 2 * s;
        ensures t5 == s4 + 2 * (s + d.full);
        ensures s + d.full < N.full;
        ensures a[s] == CPV.level_points_view(a, view.hsize)[bi][2*j];
        ensures s == CPV.point_view_index(bi, 2*j, view.hsize);
        ensures a[s+d.full] == CPV.level_points_view(a, view.hsize)[bi][2*j+1];
        ensures s+d.full == CPV.point_view_index(bi, 2*j+1, view.hsize);
    {
        s := view.higher_points_view_index_lemma(as_elems(a), d, j, bi);
        assert 2 * (bi + (2*j) * d.full) == 2 * bi + 2 * (j * (2 * d.full)) by {
            LemmaMulProperties();
        }
    }

    predicate forward_s_loop_update(
        a: seq<nat>,
        a': seq<nat>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: uint32,
        o: uint32,
        view: FNTT.loop_view)

        requires forward_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
    {
        && e < Q
        && o < Q
        && |a'| == |a|
        && s + d.full < |a|
        && a'[s + d.full] == o
        && a'[s] == e
        && a' == a[s + d.full := o][s := e]
        && assert contains_elems(a') by {
            reveal contains_elems();
        }
        && view.s_loop_update(as_elems(a), as_elems(a'), d, j, bi)
    }

    lemma forward_s_loop_inv_peri_lemma(a: seq<nat>,
        a': seq<nat>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: uint32,
        o: uint32,
        view: FNTT.loop_view)

        requires forward_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        requires forward_s_loop_update(a, a', d, j, bi, s, e, o, view);
        ensures forward_s_loop_inv(a', d, j, bi+1, view);
    {
        view.s_loop_inv_peri_lemma(a, a', d, j, bi);
        assert contains_elems(a') by {
            reveal contains_elems();
        }
    }

    lemma forward_higher_points_view_index_lemma(a: seq<nat>, d: pow2_t, j: nat, bi: nat, view: FNTT.loop_view)
        returns (s: nat)
    
        requires forward_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        ensures s == bi + (2*j) * d.full;
        ensures s + d.full < N.full;
        ensures a[s] ==
            CPV.level_points_view(as_elems(a), view.hsize)[bi][2*j];
        ensures s == CPV.point_view_index(bi, 2*j, view.hsize);
        ensures a[s+d.full] ==
            CPV.level_points_view(as_elems(a), view.hsize)[bi][2*j+1];
        ensures s+d.full == CPV.point_view_index(bi, 2*j+1, view.hsize);
    {
        s := view.higher_points_view_index_lemma(as_elems(a), d, j, bi);
    }

    lemma forward_j_loop_inv_pre_lemma(a: seq<nat>, d: pow2_t, view: FNTT.loop_view)
        requires 0 <= d.exp < N.exp;
        requires forward_t_loop_inv(a, pow2_double(d), view.coefficients);
        requires view.loop_view_wf();
        requires view.hsize == CPV.block_size(d);
        ensures forward_j_loop_inv(a, d, 0, 0, view);
    {
        view.j_loop_inv_pre_lemma(as_elems(a), d);
    }

    lemma forward_j_loop_inv_post_lemma(a: seq<nat>, d: pow2_t, j: nat, u: nat, view: FNTT.loop_view)
        requires forward_j_loop_inv(a, d, j, u, view);
        requires j == view.lsize().full;
        requires 0 <= view.hsize.exp <= N.exp;
        requires view.hsize == CPV.block_size(d);
        ensures FNTT.t_loop_inv(a, d, view.coefficients);
    {
        view.j_loop_inv_post_lemma(a, d, j);
    }

    function inverse_lsize(view: INTT.loop_view): (r: pow2_t)
        requires view.loop_view_wf();
        ensures r.full <= N.full
    {
        view.lsize()
    }

    predicate inverse_ntt_eval_all(a: seq<nat>, coeffs: seq<nat>)
    {
        && contains_elems(a)
        && contains_elems(coeffs)
        && INTT.ntt_eval_all(as_elems(a), as_elems(coeffs))
    }

    predicate inverse_t_loop_inv(a: seq<nat>, d: pow2_t, coeffs: seq<nat>)
        requires 0 <= d.exp <= N.exp;
    {
        && contains_elems(a)
        && contains_elems(coeffs)
        && INTT.t_loop_inv(as_elems(a), d, as_elems(coeffs))
    }

    predicate inverse_s_loop_inv(a: seq<nat>, d: pow2_t, j: nat, bi: nat, view: INTT.loop_view)
    {
        && contains_elems(a)
        && view.s_loop_inv(as_elems(a), d, j, bi)
    }

    predicate inverse_j_loop_inv(a: seq<nat>, d: pow2_t, j: nat, u: nat, view: INTT.loop_view)
    {
        && contains_elems(a)
        && u == j * (2 * d.full)
        && view.j_loop_inv(as_elems(a), d, j)
    }

    lemma inverse_t_loop_inv_pre_lemma(coeffs: seq<nat>)
        requires contains_elems(coeffs);
        ensures N.exp <= N.exp; // ??
        ensures inverse_t_loop_inv(coeffs, N, coeffs);
    {
        INTT.t_loop_inv_pre_lemma(as_elems(coeffs));
    }

    lemma inverse_t_loop_inv_post_lemma(a: seq<nat>, one: pow2_t, coeffs: seq<nat>)
        requires one.exp == 0 <= N.exp;
        requires inverse_t_loop_inv(a, one, coeffs);
        ensures inverse_ntt_eval_all(a, coeffs);
    {
        INTT.t_loop_inv_post_lemma(a, one, coeffs);
    }

    lemma inverse_s_loop_inv_pre_lemma(
        a: seq<nat>,
        d: pow2_t,
        j: nat,
        t: pow2_t,
        u: nat,
        ot3: uint32,
        t3: uint32,
        t6: uint32,
        s5: uint32,
        view: INTT.loop_view)

        requires inverse_j_loop_inv(a, d, j, u, view);
        requires t == view.lsize();
        requires j < view.lsize().full;
        requires t.full < BASE_32;
        requires s5 == uint32_ls(uint32_add(t.full, j), 1);
        requires t6 == 2 * d.full;
        requires ot3 == 2 * u;
        requires t3 == uint32_add(ot3, t6);

        ensures inverse_s_loop_inv(a, d, j, 0, view);
        ensures s5 == (t.full + j) * 2; 
        ensures t.full + j < N.full;
        ensures t3 == 2 * u + 2 * d.full;
        ensures INTT.rev_omega_inv_powers_mont_table()[t.full + j] == 
            MQP.mqmul(INTT.rev_omega_inv_powers_x_value(2 * j, d), R);
    {
        view.s_loop_inv_pre_lemma(as_elems(a), d, j);
        INTT.rev_omega_inv_powers_mont_table_lemma(t, d, j);
        assert uint32_add(t.full, j) == t.full + j;
        ls1_is_double(t.full + j);
        // rev_omega_inv_powers_mont_table_lemma(t, d, j);

        assert u == j * (2 * d.full);
        assert d == view.hcount();

        calc {
            j * (2 * d.full) + d.full;
            <= 
            {
                LemmaMulInequality(j, 512, 2 * d.full);
            }
            512 * (2 * d.full) + d.full;
        }
    }

    lemma inverse_s_loop_inv_post_lemma(
        a: seq<nat>,
        d: pow2_t,
        j: nat,
        u: uint32,
        bi: nat,
        ot3: uint32,
        t3: uint32,
        t6: uint32,
        view: INTT.loop_view)

        requires bi == d.full;
        requires t6 == 2 * d.full;
        requires u == j * (2 * d.full);
        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires ot3 == 2 * u + 2 * d.full;
        requires t3 == uint32_add(ot3, t6);
        ensures t3 == 2 * (u + 2 * d.full);
        ensures inverse_j_loop_inv(a, d, j + 1, u + 2 * d.full, view);
    {
        view.s_loop_inv_post_lemma(as_elems(a), d, j, bi);

        assert u + 2 * d.full == (j + 1) * (2 * d.full) by {
            LemmaMulProperties();
        }

        calc == {
            ot3 + t6;
            2 * u + 2 * d.full + 2 * d.full;
            2 * (j * (2 * d.full)) + 2 * d.full + 2 * d.full;
            {
                LemmaMulProperties();
            }
            (2 * j + 2) * (2 * d.full);
        }

        assert d == view.hcount();

        calc {
            (2 * j + 2) * (2 * d.full);
            <= 
            {
                LemmaMulInequality(2 * j + 2, 1024, 2 * d.full);
            }
            1024 * (2 * d.full);
            <
            {
                assert d.full <= 512;
            }
            BASE_31;
        }
    }

    lemma inverse_s_loop_index_lemma(
        a: seq<nat>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s4: uint32,
        s2: uint32,
        t4: uint32,
        t5: uint32,
        t6: uint32,
        view: INTT.loop_view)
        returns (s: nat)

        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        requires s2 == 2 * bi + 2 * (j * (2 * d.full)); 
        requires flat.ptr_admissible_32(heap_b32_index_ptr(s4, N.full / 2 - 1));
        requires t4 == uint32_add(s4, s2);
        requires t5 == uint32_add(t4, t6);
        requires t6 == 2 * d.full;

        ensures s == bi + (2*j) * d.full;
        ensures t4 == s4 + 2 * s;
        ensures t5 == s4 + 2 * (s + d.full);
        ensures s + d.full < N.full;
        ensures a[s] == CPV.level_points_view(a, view.hsize)[bi][2*j];
        ensures s == CPV.point_view_index(bi, 2*j, view.hsize);
        ensures a[s+d.full] == CPV.level_points_view(a, view.hsize)[bi][2*j+1];
        ensures s+d.full == CPV.point_view_index(bi, 2*j+1, view.hsize);
    {
        s := view.higher_points_view_index_lemma(as_elems(a), d, j, bi);
        assert 2 * (bi + (2*j) * d.full) == 2 * bi + 2 * (j * (2 * d.full)) by {
            LemmaMulProperties();
        }
    }

    predicate inverse_s_loop_update(
        a: seq<nat>,
        a': seq<nat>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: uint32,
        o: uint32,
        view: INTT.loop_view)

        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
    {
        && e < Q
        && o < Q
        && |a'| == |a|
        && s + d.full < |a|
        && a'[s + d.full] == o
        && a'[s] == e
        && a' == a[s + d.full := o][s := e]
        && assert contains_elems(a') by {
            reveal contains_elems();
        }
        && view.s_loop_update(as_elems(a), as_elems(a'), d, j, bi)
    }

    lemma inverse_s_loop_inv_peri_lemma(a: seq<nat>,
        a': seq<nat>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: uint32,
        o: uint32,
        view: INTT.loop_view)

        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        requires inverse_s_loop_update(a, a', d, j, bi, s, e, o, view);
        ensures inverse_s_loop_inv(a', d, j, bi+1, view);
    {
        view.s_loop_inv_peri_lemma(a, a', d, j, bi);
        assert contains_elems(a') by {
            reveal contains_elems();
        }
    }

    lemma inverse_higher_points_view_index_lemma(a: seq<nat>, d: pow2_t, j: nat, bi: nat, view: INTT.loop_view)
        returns (s: nat)
    
        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        ensures s == bi + (2*j) * d.full;
        ensures s + d.full < N.full;
        ensures a[s] ==
            CPV.level_points_view(as_elems(a), view.hsize)[bi][2*j];
        ensures s == CPV.point_view_index(bi, 2*j, view.hsize);
        ensures a[s+d.full] ==
            CPV.level_points_view(as_elems(a), view.hsize)[bi][2*j+1];
        ensures s+d.full == CPV.point_view_index(bi, 2*j+1, view.hsize);
    {
        s := view.higher_points_view_index_lemma(as_elems(a), d, j, bi);
    }

    lemma inverse_j_loop_inv_pre_lemma(a: seq<nat>, d: pow2_t, view: INTT.loop_view)
        requires 0 <= d.exp < N.exp;
        requires inverse_t_loop_inv(a, pow2_double(d), view.coefficients);
        requires view.loop_view_wf();
        requires view.hsize == CPV.block_size(d);
        ensures inverse_j_loop_inv(a, d, 0, 0, view);
    {
        view.j_loop_inv_pre_lemma(as_elems(a), d);
    }

    lemma inverse_j_loop_inv_post_lemma(a: seq<nat>, d: pow2_t, j: nat, u: nat, view: INTT.loop_view)
        requires inverse_j_loop_inv(a, d, j, u, view);
        requires j == view.lsize().full;
        requires 0 <= view.hsize.exp <= N.exp;
        requires view.hsize == CPV.block_size(d);
        ensures INTT.t_loop_inv(a, d, view.coefficients);
    {
        view.j_loop_inv_post_lemma(a, d, j);
    }

    function bit_rev_view_init(a: seq<nat>): (view: rev_view)
        requires |a| == N.full;
        ensures view.len == N;
        ensures view.shuffle_inv(a);
    {
        var view := rev_view.init_rev_view(a, N);
        view.shuffle_inv_pre_lemma(a, N);
        view
    }

    lemma bit_rev_index_lemma(
        a: seq<nat>,
        ftable: seq<nat>,
        sbi: uint32,
        rsbi: uint32,
        ti: nat,
        a0: uint32,
        t0: uint32,
        t1: uint32)

        requires |a| == N.full;
        requires bit_rev_ftable_wf(ftable);

        requires 0 <= 2 * ti + 1 < |ftable|;
        requires sbi == ftable[2 * ti];
        requires rsbi == ftable[2 * ti+1];
    
        requires flat.ptr_admissible_32(heap_b32_index_ptr(a0, N.full / 2 - 1));

        requires t0 == uint32_add(a0, uint32_ls(sbi, 1));
        requires t1 == uint32_add(a0, uint32_ls(rsbi, 1));

        ensures t0 == a0 + 2 * sbi;
        ensures t1 == a0 + 2 * rsbi;

        ensures sbi == build_view(a, ti, N).get_split_index();
        ensures rsbi == bit_rev_int(ftable[2 * ti], N);
    {
        var table := ftable_cast(ftable);
        assert ti < |table|;

        assert table[ti].0 == ftable[2 * ti]
            && table[ti].1 == ftable[2 * ti + 1] by {
            reveal ftable_cast();
        }

        assert table[ti].0 == build_view(a, ti, N).get_split_index()
            && table[ti].1 == bit_rev_int(table[ti].0, N) by {
            reveal table_wf();
            reveal table_wf_inner();
        }

        // ftable_index_lemma(a, ftable, table, ti);
        assert sbi == build_view(a, ti, N).get_split_index();
        assert rsbi == bit_rev_int(ftable[2 * ti], N);

        ls1_is_double(sbi);
        ls1_is_double(rsbi);
    }

    lemma bit_rev_view_inv_peri_lemma(
        a: seq<nat>,
        next_b: seq<nat>,
        view: rev_view,
        table: seq<nat>)
        returns (next_view: rev_view)

        requires contains_elems(view.b);
        requires |a| == N.full;
        requires bit_rev_ftable_wf(table);
        requires view.len == N;
        requires view.shuffle_inv(a);
        requires next_b == view.next_rev_buffer();

        requires 2 * view.ti < |init_unfinished(N)|;
        ensures next_view == view.next_rev_view(a);
        ensures next_view.shuffle_inv(a);
        ensures next_view.b == next_b;
        ensures contains_elems(next_view.b);
    {
        next_view := view.next_rev_view(a);
        view.shuffle_inv_peri_lemma(a, next_view);
        reveal contains_elems();
    }

    lemma bit_rev_view_inv_post_lemma(a: seq<nat>, view: rev_view)

        requires |a| == N.full;
        requires view.len == N;
        requires view.shuffle_inv(a);
        requires 2 * view.ti == |init_unfinished(N)|; 
        ensures is_bit_rev_shuffle(a, view.b, N);
    {
        view.shuffle_inv_post_lemma(a);
    }

    predicate circle_product_inv(a: seq<nat>, init_a: seq<nat>, b: seq<nat>, i: nat)
    {
        && contains_elems(init_a)
        && contains_elems(b)
        && i <= |init_a| == |a| == |b| == N.full
        && init_a[i..] == a[i..]
        && reveal contains_elems();
        && (forall j: nat | 0 <= j < i :: a[j] == MQP.mqmul(init_a[j], b[j]))
    }

    lemma circle_product_inv_peri_lemma(
        a: seq<nat>, 
        init_a: seq<nat>,
        ai: uint32,
        b: seq<nat>,
        i: nat)

        requires i < N.full;
        requires circle_product_inv(a, init_a, b, i);
        requires init_a[i] < Q;
        requires b[i] < Q;
        requires ai == MQP.montmul(MQP.montmul(init_a[i], 10952), b[i]);
        ensures  circle_product_inv(a[i := ai], init_a, b, i+1);
    {
        var next_a := a[i := ai];
        forall j: nat | 0 <= j < i+1
            ensures next_a[j] == MQP.mqmul(init_a[j], b[j])
        {
            if j != i {
                assert next_a[j] == a[j];
            } else {
                assert next_a[j] == ai;
                assume ai == MQP.mqmul(init_a[j], b[j]);
            }
        }
    }

    predicate mq_poly_scale_inv(a: seq<nat>, init_a: seq<nat>, b: seq<nat>, i: nat)
    {
        && contains_elems(init_a)
        && contains_elems(b)
        && reveal contains_elems();
        && i <= |init_a| == |a| == |b| == N.full
        && init_a[i..] == a[i..]
        && (forall j: nat | 0 <= j < i :: a[j] == MQP.montmul(init_a[j], b[j]))
    }

    lemma mq_poly_scale_peri_lemma(
        a: seq<nat>, 
        init_a: seq<nat>,
        ai: uint32,
        b: seq<nat>,
        i: nat)

        requires i < N.full;
        requires mq_poly_scale_inv(a, init_a, b, i);
        requires init_a[i] < Q;
        requires b[i] < Q;
        requires ai == MQP.montmul(init_a[i], b[i]);
        ensures  mq_poly_scale_inv(a[i := ai], init_a, b, i+1);
    {
        var next_a := a[i := ai];
        forall j: nat | 0 <= j < i+1
            ensures next_a[j] == MQP.montmul(init_a[j], b[j])
        {
            if j != i {
                assert next_a[j] == a[j];
            } else {
                assert next_a[j] == ai;
            }
        }
    }

    lemma mq_ntt_mul_lemma(
        a0: seq<nat>,
        a1: seq<nat>,
        b0: seq<nat>,
        b1: seq<nat>,
        p0: seq<nat>,
        p1: seq<nat>,
        p2: seq<nat>,
        p3: seq<nat>,
        p4: seq<nat>)

        requires contains_elems(p0);
        requires contains_elems(p1);
        requires contains_elems(p2);
        requires contains_elems(p3);
        requires contains_elems(p4);

        requires forward_ntt_eval_all(a1, a0);
        requires forward_ntt_eval_all(b1, b0);
        requires circle_product_inv(p0, a1, b1, N.full);
        requires is_bit_rev_shuffle(p0, p1, N);

        requires inverse_ntt_eval_all(p2, p1);
        requires is_bit_rev_shuffle(p2, p3, N);

        requires mq_poly_scale_inv(p4, p3, MQP.inverse_ntt_scaling_table(), N.full);

        ensures p4 == poly_mod_product(a0, b0)
        // MQP.poly_mod_equiv(p4, MQP.poly_mul(a0, b0), MQP.n_ideal());
    {
        assume false;
    }

    predicate uint16_is_normalized(e: uint16)
    {
        MQN.int_is_normalized(bv16_op_s.to_int16(e))
    }

    // bascially convert to int16, but with requires
    // DOES NOT normalize a value
    // ONLY interprets an uint16 as a normalized value
    function uint16_as_nelem(e: uint16): nelem
        requires uint16_is_normalized(e)
    {
        bv16_op_s.to_int16(e)
    }

    predicate {:opaque} normalized_values(a: seq<uint16>)
        ensures normalized_values(a) ==> |a| == N.full;
    {
        && |a| == N.full
        && (forall i | 0 <= i < |a| :: uint16_is_normalized(a[i]))
    }

    function as_nelems(a: seq<uint16>): (na: seq<nelem>)
        requires normalized_values(a);
    {
        reveal normalized_values();
        seq(|a|, i requires 0 <= i < |a| => uint16_as_nelem(a[i]))
    }

    predicate normalized_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(iter, heap, if address >= 0 then address else iter.cur_ptr())
        && (index >= 0 ==> iter.index == index)
        && normalized_values(iter.buff)
    }

    lemma denormalize_lemma(buff: seq<uint16>, i: nat, a1: uint32, b: uint32, c: uint32, d: uint32)
        requires normalized_values(buff);
        requires i < |buff|;
        requires a1 == uint16_sign_ext(buff[i]);
        requires b == uint32_srai(a1, 31);
        requires c == uint32_and(b, Q);
        requires d == uint32_add(a1, c);
        ensures uint16_is_normalized(buff[i]);
        ensures d == MQN.denormalize(uint16_as_nelem(buff[i]));
    {
        assert uint16_is_normalized(buff[i]) by {
            reveal normalized_values();
        }

        var a0 :uint16 := buff[i];
        var sa0 := uint16_as_nelem(a0);
        assert sa0 < 0 ==> a1 == a0 as nat + 0xffff0000;
        assert sa0 >= 0 ==> a1 == a0;

        if to_int32(a1) >= 0 {
            assert sa0 >= 0;
            assert b == 0 by { lemma_rs_by_31(to_int32(a1)); }
            lemma_uint32_and_Q(b);
            assert c == 0;
            assert d == a0;
            assert d == MQN.denormalize(uint16_as_nelem(a0));
        }
        else {
            assert sa0 < 0;
            assert int32_rs(to_int32(a1), 31) == -1 by { lemma_rs_by_31(to_int32(a1)); }
            lemma_uint32_and_Q(b);
            assert c == Q;
            assert d == sa0 + Q;
            assert d == MQN.denormalize(uint16_as_nelem(a0));
        }
    }

    predicate {:opaque} denormalization_inv(nv: seq<uint16>, dnv: seq<uint16>, i: nat)
        requires normalized_values(nv);
        requires contains_elems(dnv);
    {
        && reveal normalized_values();
        && i <= N.full
        && (forall j | 0 <= j < i :: 
            dnv[j] == MQN.denormalize(uint16_as_nelem(nv[j])))
    }

    lemma denormalization_pre_lemma(nv: seq<uint16>, dnv: seq<uint16>)
        requires normalized_values(nv);
        requires contains_elems(dnv);
        ensures denormalization_inv(nv, dnv, 0);
    {
        reveal denormalization_inv();
    }

    lemma denormalization_peri_lemma(buff: seq<uint16>, dnv: seq<uint16>, i: nat, a1: uint32, b: uint32, c: uint32, d: uint32)
        requires normalized_values(buff);
        requires contains_elems(dnv);
        requires denormalization_inv(buff, dnv, i);
        requires i < |buff|;
        requires a1 == uint16_sign_ext(buff[i]);
        requires b == uint32_srai(a1, 31);
        requires c == uint32_and(b, Q);
        requires d == uint32_add(a1, c);
        ensures uint16_is_normalized(buff[i]);
        ensures d == MQN.denormalize(uint16_as_nelem(buff[i]));
        ensures contains_elems(dnv[i := lh(d)]);
        ensures denormalization_inv(buff, dnv[i := lh(d)], i + 1);
    {
        reveal denormalization_inv();
        reveal normalized_values();
        reveal contains_elems();

        var lh, uh := lh(d), uh(d);
        half_split_lemma(d);
        assume uh == 0;
        denormalize_lemma(buff, i, a1, b, c, d);
        assert d == lh;
    }
    
    // 0 <= e < Q -> -Q/2 <= e <= Q/2
    predicate {:opaque} normalization_inv(outputs: seq<uint16>,  inputs: seq<uint16>, i: nat)
    {
        && contains_elems(inputs)
        && |outputs| == N.full
        && reveal contains_elems();
        && i <= N.full
        && inputs[i..] == outputs[i..]
        && (forall j | 0 <= j < i :: (
            && uint16_is_normalized(outputs[j])
            && uint16_as_nelem(outputs[j]) == MQN.normalize(inputs[j]))
        )
    }

    lemma normalization_pre_lemma(inputs: seq<uint16>)
        requires contains_elems(inputs);
        ensures normalization_inv(inputs, inputs, 0);
    {
        reveal normalization_inv();
    }

    lemma normalization_peri_lemma(outputs: seq<uint16>, inputs: seq<uint16>, i: nat, a: uint32, b: uint32, c: uint32, d: uint32, e: uint32)
        requires normalization_inv(outputs, inputs, i);
        requires i < |outputs|;
        requires a == outputs[i];
        requires b == uint32_sub(Q/2, a);
        requires c == uint32_srai(b, 31);
        requires d == uint32_and(c, Q);
        requires e == uint32_sub(a, d);
        ensures normalization_inv(outputs[i := lh(e)], inputs, i + 1);
    // {
    //     reveal contains_elems();
    //     reveal normalization_inv();

    //     assert outputs[i] == inputs [i];

    //     cond_set_Q_lemma(b, d);

    //     var lh, uh := lh(e), uh(e);
    //     half_split_lemma(e);

    //     if to_int32(b) >= 0 {
    //         assert d == 0;
    //         assume uh == 0; // the upper bits all clear
    //         assert uint16_as_nelem(e) == MQN.normalize(a);
    //     } else {
    //         assert d == Q;
    //         assert 0 <= a < Q;
    //         assert to_int32(b) == Q_HLAF - a;
    //         assert Q_HLAF < a;
    //         assert to_int32(e) == a as int - Q;
    //         assert -Q_HLAF <= to_int32(e) <= Q_HLAF;
    //         if to_int32(e) < 0 {
    //             assume uh == 0xffff; // the upper bits all set
    //         } else {
    //             assume uh == 0; // the upper bits all clear
    //         }
    //         assert bv16_op_s.to_int16(lh) == to_int32(e);
    //     }
    //     assert uint16_as_nelem(lh) == MQN.normalize(a);
    // }

    lemma normalization_post_lemma(outputs: seq<uint16>, inputs: seq<uint16>)
        requires contains_elems(inputs);
        requires normalization_inv(outputs, inputs, 512);
        ensures normalized_values(outputs);
    {
        reveal normalization_inv();
        reveal normalized_values();
    }

    const NORMSQ_BOUND := integers.BASE_31

    predicate l2norm_squared_bounded_inv(norm: uint32, 
        s1: seq<uint16>, s2: seq<uint16>, i: nat, ng: uint32)
    {
        && normalized_values(s1)
        && normalized_values(s2)
        && var ns1 := as_nelems(s1);
        && var ns2 := as_nelems(s2);
        && i <= N.full
        && ((msb(ng) == 0) ==> (norm == MQN.l2norm_squared(ns1, ns2, i)))
        && ((msb(ng) == 1) ==> (MQN.l2norm_squared(ns1, ns2, i) >= NORMSQ_BOUND))
    }

    lemma l2norm_squared_bounded_pre_lemma(s1: seq<uint16>, s2: seq<uint16>)
        requires normalized_values(s1)
        requires normalized_values(s2)
        ensures l2norm_squared_bounded_inv(0, s1, s2, 0, 0);
    {
        assume msb(0) == 0;
    }

    lemma l2norm_squared_bounded_peri_lemma(
        norm0: uint32, norm1: uint32, norm2: uint32,
        ng0: uint32, ng1: uint32, ng2: uint32,
        v1: uint32, v2: uint32,
        vv1: uint32, vv2: uint32,
        s1: seq<uint16>, s2: seq<uint16>,
        i: nat)

        requires l2norm_squared_bounded_inv(norm0, s1, s2, i, ng0);
        requires i < N.full
        requires v1 == uint16_sign_ext(s1[i])
        requires v2 == uint16_sign_ext(s2[i])
        requires vv1 == uint32_mul(v1, v1);
        requires vv2 == uint32_mul(v2, v2);

        requires norm1 == uint32_add(norm0, vv1);
        requires norm2 == uint32_add(norm1, vv2);
        requires ng1 == uint32_or(ng0, norm1);
        requires ng2 == uint32_or(ng1, norm2);

        ensures l2norm_squared_bounded_inv(norm2, s1, s2, i+1, ng2);
    {
        reveal normalized_values();
        var iv1, iv2 := uint16_as_nelem(s1[i]), uint16_as_nelem(s2[i]);
        var ivv1, ivv2 := iv1 as int * iv1 as int, iv2 as int * iv2 as int;
        assume vv1 == ivv1;
        assume vv2 == ivv2;

        msb_bound_lemma(norm0);
        msb_bound_lemma(norm1);
        msb_bound_lemma(norm2);

        if msb(ng0) == 1 {
            assume msb(ng2) == 1; 
            return;
        }

        if msb(ng1) == 1 {
            assume msb(norm1) == 1;
            assume msb(ng2) == 1;
            return;
        }

        if msb(ng2) == 1 {
            assume msb(norm2) == 1;
            return;
        }

        assume msb(norm2) == 0;
        assume msb(norm1) == 0;
        assume msb(norm0) == 0;

        assume vv1 <= 0x80000000;
        assume vv2 <= 0x80000000;

        return; 
    }

    predicate l2norm_squared_result(s1: seq<uint16>, s2: seq<uint16>, result: uint32)
    {
        && normalized_values(s1)
        && normalized_values(s2)
        && ((result == 1) <==> (MQN.l2norm_squared(as_nelems(s1), as_nelems(s2), |s1|) < 0x29845d6))
    }

    lemma l2norm_squared_bounded_post_lemma(s1: seq<uint16>, s2: seq<uint16>, norm0: uint32, ng: uint32, norm1: uint32, result: uint32)
        requires l2norm_squared_bounded_inv(norm0, s1, s2, 512, ng);
        requires norm1 == uint32_or(norm0, uint32_srai(ng, 31));
        requires result == uint32_lt(norm1, 0x29845d6);
        ensures l2norm_squared_result(s1, s2, result);
    {
        if (msb(ng) == 0) {
            assume uint32_srai(ng, 31) == 0;
            assume norm1 == norm0;
        } else {
            assume uint32_srai(ng, 31) == 0xffff_ffff;
            assume norm1 == 0xffff_ffff;
        }
    }

    lemma rv_falcon_512_lemma(tt0: seq<uint16>, tt1: seq<uint16>, tt2: seq<uint16>, s1: seq<uint16>, s2: seq<uint16>, h: seq<uint16>, c0: seq<uint16>, result: uint32)
        requires l2norm_squared_result(s1, s2, result);
        requires contains_elems(tt0);
        requires contains_elems(c0);
        requires contains_elems(h);
        requires denormalization_inv(s2, tt0, 512);
        // requires tt1 == poly_mod_product(tt0, h);
        requires poly_sub_loop_inv(tt2, tt1, c0, 512);
        requires normalization_inv(s1, tt2, 512);
        ensures (result == 1) <==> falcon_verify(
            as_elems(c0), as_nelems(s2), as_elems(h));
    // {
    //     reveal denormalization_inv();
    //     assert tt0 == MQN.denormalize_n_elems(as_nelems(s2));
    //     assert tt1 == MQP.poly_mod(MQP.poly_mul(tt0, h), MQP.n_ideal());
    //     assume c0 == as_elems(c0);
    //     assume h == as_elems(h);
    //     assert tt2 == MQP.poly_sub(tt1, c0);
    //     reveal normalization_inv();
    //     assert as_nelems(s1) == MQN.normalize_elems(tt2);
    //     assert falcon_512_i.bound() == 0x29845d6;
    // }

}
