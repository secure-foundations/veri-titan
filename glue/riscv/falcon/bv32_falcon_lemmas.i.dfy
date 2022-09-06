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
        && buff_is_n_elems(iter.buff)
    }

    function forward_lsize(view: FNTT.loop_view): (r: pow2_t)
        requires view.loop_view_wf();
        ensures r.full <= N.full
    {
        view.lsize()
    }

    predicate forward_ntt_eval_all(a: seq<nat>, coeffs: seq<nat>)
    {
        && buff_is_n_elems(a)
        && buff_is_n_elems(coeffs)
        && FNTT.ntt_eval_all(buff_as_n_elems(a), buff_as_n_elems(coeffs))
    }

    predicate forward_ntt_eval_all_alt(p: seq<nat>, a: seq<nat>)
    {
        && buff_is_n_elems(a)
        && buff_is_n_elems(p)
        && var a_hat := MQP.scaled_coeff(buff_as_n_elems(a));
        && (forall i | 0 <= i < N.full ::
            MQP.poly_eval(a_hat, MQP.mqpow(MQ.OMEGA, bit_rev_int(i, N))) == p[i])
    }

    predicate forward_t_loop_inv(a: seq<nat>, d: pow2_t, coeffs: seq<nat>)
        requires 0 <= d.exp <= N.exp;
    {
        && buff_is_n_elems(a)
        && buff_is_n_elems(coeffs)
        && FNTT.t_loop_inv(buff_as_n_elems(a), d, buff_as_n_elems(coeffs))
    }

    predicate forward_s_loop_inv(a: seq<nat>, d: pow2_t, j: nat, bi: nat, view: FNTT.loop_view)
    {
        && buff_is_n_elems(a)
        && view.s_loop_inv(buff_as_n_elems(a), d, j, bi)
    }

    predicate forward_j_loop_inv(a: seq<nat>, d: pow2_t, j: nat, u: nat, view: FNTT.loop_view)
    {
        && buff_is_n_elems(a)
        && u == j * (2 * d.full)
        && view.j_loop_inv(buff_as_n_elems(a), d, j)
    }

    lemma forward_t_loop_inv_pre_lemma(coeffs: seq<nat>)
        requires buff_is_n_elems(coeffs);
        ensures N.exp <= N.exp; // ??
        ensures forward_t_loop_inv(coeffs, N, coeffs);
    {
        FNTT.t_loop_inv_pre_lemma(buff_as_n_elems(coeffs));
    }

    lemma forward_t_loop_inv_post_lemma(a: seq<nat>, one: pow2_t, coeffs: seq<nat>)
        requires one.exp == 0 <= N.exp;
        requires forward_t_loop_inv(a, one, coeffs);
        ensures forward_ntt_eval_all(a, coeffs);
    {
        FNTT.t_loop_inv_post_lemma(a, one, coeffs);
    }

    function mqmul(a: elem, b: elem): elem
    {
        MQP.mqmul(a, b)
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
        view.s_loop_inv_pre_lemma(buff_as_n_elems(a), d, j);
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
        view.s_loop_inv_post_lemma(buff_as_n_elems(a), d, j, bi);

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
        s := view.higher_points_view_index_lemma(buff_as_n_elems(a), d, j, bi);
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
        && assert buff_is_n_elems(a') by {
            reveal buff_is_n_elems();
        }
        && view.s_loop_update(buff_as_n_elems(a), buff_as_n_elems(a'), d, j, bi)
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
        assert buff_is_n_elems(a') by {
            reveal buff_is_n_elems();
        }
    }

    lemma forward_higher_points_view_index_lemma(a: seq<nat>, d: pow2_t, j: nat, bi: nat, view: FNTT.loop_view)
        returns (s: nat)
    
        requires forward_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        ensures s == bi + (2*j) * d.full;
        ensures s + d.full < N.full;
        ensures a[s] ==
            CPV.level_points_view(buff_as_n_elems(a), view.hsize)[bi][2*j];
        ensures s == CPV.point_view_index(bi, 2*j, view.hsize);
        ensures a[s+d.full] ==
            CPV.level_points_view(buff_as_n_elems(a), view.hsize)[bi][2*j+1];
        ensures s+d.full == CPV.point_view_index(bi, 2*j+1, view.hsize);
    {
        s := view.higher_points_view_index_lemma(buff_as_n_elems(a), d, j, bi);
    }

    lemma forward_j_loop_inv_pre_lemma(a: seq<nat>, d: pow2_t, view: FNTT.loop_view)
        requires 0 <= d.exp < N.exp;
        requires forward_t_loop_inv(a, pow2_double(d), view.coefficients);
        requires view.loop_view_wf();
        requires view.hsize == CPV.block_size(d);
        ensures forward_j_loop_inv(a, d, 0, 0, view);
    {
        view.j_loop_inv_pre_lemma(buff_as_n_elems(a), d);
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
        && buff_is_n_elems(a)
        && buff_is_n_elems(coeffs)
        && INTT.ntt_eval_all(buff_as_n_elems(a), buff_as_n_elems(coeffs))
    }

    predicate inverse_t_loop_inv(a: seq<nat>, d: pow2_t, coeffs: seq<nat>)
        requires 0 <= d.exp <= N.exp;
    {
        && buff_is_n_elems(a)
        && buff_is_n_elems(coeffs)
        && INTT.t_loop_inv(buff_as_n_elems(a), d, buff_as_n_elems(coeffs))
    }

    predicate inverse_s_loop_inv(a: seq<nat>, d: pow2_t, j: nat, bi: nat, view: INTT.loop_view)
    {
        && buff_is_n_elems(a)
        && view.s_loop_inv(buff_as_n_elems(a), d, j, bi)
    }

    predicate inverse_j_loop_inv(a: seq<nat>, d: pow2_t, j: nat, u: nat, view: INTT.loop_view)
    {
        && buff_is_n_elems(a)
        && u == j * (2 * d.full)
        && view.j_loop_inv(buff_as_n_elems(a), d, j)
    }

    lemma inverse_t_loop_inv_pre_lemma(coeffs: seq<nat>)
        requires buff_is_n_elems(coeffs);
        ensures N.exp <= N.exp; // ??
        ensures inverse_t_loop_inv(coeffs, N, coeffs);
    {
        INTT.t_loop_inv_pre_lemma(buff_as_n_elems(coeffs));
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
        view.s_loop_inv_pre_lemma(buff_as_n_elems(a), d, j);
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
        view.s_loop_inv_post_lemma(buff_as_n_elems(a), d, j, bi);

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
        s := view.higher_points_view_index_lemma(buff_as_n_elems(a), d, j, bi);
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
        && assert buff_is_n_elems(a') by {
            reveal buff_is_n_elems();
        }
        && view.s_loop_update(buff_as_n_elems(a), buff_as_n_elems(a'), d, j, bi)
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
        assert buff_is_n_elems(a') by {
            reveal buff_is_n_elems();
        }
    }

    lemma inverse_higher_points_view_index_lemma(a: seq<nat>, d: pow2_t, j: nat, bi: nat, view: INTT.loop_view)
        returns (s: nat)
    
        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        ensures s == bi + (2*j) * d.full;
        ensures s + d.full < N.full;
        ensures a[s] ==
            CPV.level_points_view(buff_as_n_elems(a), view.hsize)[bi][2*j];
        ensures s == CPV.point_view_index(bi, 2*j, view.hsize);
        ensures a[s+d.full] ==
            CPV.level_points_view(buff_as_n_elems(a), view.hsize)[bi][2*j+1];
        ensures s+d.full == CPV.point_view_index(bi, 2*j+1, view.hsize);
    {
        s := view.higher_points_view_index_lemma(buff_as_n_elems(a), d, j, bi);
    }

    lemma inverse_j_loop_inv_pre_lemma(a: seq<nat>, d: pow2_t, view: INTT.loop_view)
        requires 0 <= d.exp < N.exp;
        requires inverse_t_loop_inv(a, pow2_double(d), view.coefficients);
        requires view.loop_view_wf();
        requires view.hsize == CPV.block_size(d);
        ensures inverse_j_loop_inv(a, d, 0, 0, view);
    {
        view.j_loop_inv_pre_lemma(buff_as_n_elems(a), d);
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

    function {:opaque} ftable_cast(ftable: seq<nat>): (r: seq<(nat, nat)>)
        requires |ftable| == |init_unfinished(N)|;
        ensures |r| == |init_unfinished(N)| / 2;
    {
        var size := |init_unfinished(N)| / 2;
        seq(size, i requires 0 <= i < size => (ftable[2 * i], ftable[2 * i + 1]))
    }

    predicate bit_rev_ftable_wf(ftable: seq<nat>)
    {
        && |ftable| == |init_unfinished(N)|
        && table_wf(ftable_cast(ftable), N)
    }

    predicate bit_rev_shuffle_inv(a: seq<nat>, view: rev_view)
        requires |a| == view.len.full;
    {
       view.shuffle_inv(a)
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

        requires buff_is_n_elems(view.b);
        requires |a| == N.full;
        requires bit_rev_ftable_wf(table);
        requires view.len == N;
        requires view.shuffle_inv(a);
        requires next_b == view.next_rev_buffer();

        requires 2 * view.ti < |init_unfinished(N)|;
        ensures next_view == view.next_rev_view(a);
        ensures next_view.shuffle_inv(a);
        ensures next_view.b == next_b;
        ensures buff_is_n_elems(next_view.b);
    {
        next_view := view.next_rev_view(a);
        view.shuffle_inv_peri_lemma(a, next_view);
        reveal buff_is_n_elems();
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

    predicate mq_ntt_poly_mul_inv(a: seq<nat>, init_a: seq<nat>, b: seq<nat>, i: nat)
    {
        && buff_is_n_elems(init_a)
        && buff_is_n_elems(b)
        && i <= |init_a| == |a| == |b| == N.full
        && init_a[i..] == a[i..]
        && reveal buff_is_n_elems();
        && (forall j: nat | 0 <= j < i :: a[j] == MQP.mqmul(init_a[j], b[j]))
    }

    lemma mq_ntt_poly_mul_inv_peri_lemma(
        a: seq<nat>, 
        init_a: seq<nat>,
        ai: uint32,
        b: seq<nat>,
        i: nat)

        requires i < N.full;
        requires mq_ntt_poly_mul_inv(a, init_a, b, i);
        requires init_a[i] < Q;
        requires b[i] < Q;
        requires ai == MQP.montmul(MQP.montmul(init_a[i], 10952), b[i]);
        ensures  mq_ntt_poly_mul_inv(a[i := ai], init_a, b, i+1);
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
        && buff_is_n_elems(init_a)
        && buff_is_n_elems(b)
        && reveal buff_is_n_elems();
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

    lemma forward_ntt_lemma(
        p: seq<nat>,
        a: seq<nat>)

        requires forward_ntt_eval_all(p, a);
        ensures forward_ntt_eval_all_alt(p, a)
    {
       var a_hat: seq<elem> := MQP.scaled_coeff(a);

        forall i | 0 <= i < N.full
            ensures MQP.poly_eval(a_hat, MQP.mqpow(PSI, 2 * bit_rev_int(i, N))) == p[i];
        {
            var index := 2 * bit_rev_int(i, N);
            var x := MQP.mqpow(PSI, index);
            var x_hat := MQP.mqpow(PSI, index + 1);

            var left := MQP.poly_terms(a, x_hat);
            var right := MQP.poly_terms(a_hat, x);

            assert MQP.poly_eval(a, x_hat) == p[i] by {
                reveal CPV.points_eval_suffix_inv();
                assert index * 1 == index;
            }

            assert left == right by {
                forall j | 0 <= j < N.full 
                    ensures left[j] == right[j];
                {
                    var x_j := MQP.mqpow(x, j);

                    LemmaMulStrictlyPositive(index, j);

                    assert x_j == MQP.mqpow(PSI, index * j) by {
                        MQP.mqpow_muls(PSI, index, j);
                    }

                    calc == {
                        left[j];
                        MQP.mqmul(a[j], MQP.mqpow(x_hat, j));
                        MQP.mqmul(a[j], MQP.mqpow(MQP.mqpow(PSI, index + 1), j));
                        {
                            MQP.mqpow_muls(PSI, index + 1, j);
                        }
                        MQP.mqmul(a[j], MQP.mqpow(PSI, (index + 1) * j));
                        {
                            LemmaMulIsDistributiveAddOtherWayAuto();
                        }
                        MQP.mqmul(a[j], MQP.mqpow(PSI, index * j + j));
                        {
                            MQP.mqpow_adds(PSI, index * j, j);
                        }
                        MQP.mqmul(a[j], MQP.mqmul(x_j, MQP.mqpow(PSI, j)));
                        {
                            MQP.mqmul_commutes(x_j, MQP.mqpow(PSI, j));
                        }
                        MQP.mqmul(a[j], MQP.mqmul(MQP.mqpow(PSI, j), x_j));
                        {
                            MQP.mqmul_associates(a[j], MQP.mqpow(PSI, j), x_j);
                        }
                        MQP.mqmul(MQP.mqmul(a[j], MQP.mqpow(PSI, j)), x_j);
                        MQP.mqmul(a_hat[j], MQP.mqpow(x, j));
                        right[j];
                    }
                }
            }

            assert MQP.poly_eval(a_hat, x) == p[i] by {
                reveal MQP.poly_eval();
                calc == {
                    MQP.poly_eval(a, x_hat);
                    MQP.mqsum(left);
                    MQP.mqsum(right);
                    MQP.poly_eval(a_hat, x);
                }
            }
        }

        forall i | 0 <= i < N.full
            ensures MQP.poly_eval(a_hat, MQP.mqpow(MQ.OMEGA, bit_rev_int(i, N))) == p[i];
        {
            var index := bit_rev_int(i, N);
            calc == {
                MQP.mqpow(PSI, 2 * index);
                Pow(PSI, 2 * index) % Q;
                {
                    LemmaPowMultiplies(PSI, 2, index);
                }
                Pow(Pow(PSI, 2), index) % Q;
                {
                    LemmaPowModNoop(Pow(PSI, 2), index, Q);
                }
                Pow(Pow(PSI, 2) % Q, index) % Q;
                {
                    MQ.Nth_root_lemma();
                }
                Pow(MQ.OMEGA % Q, index) % Q;
                {
                    LemmaPowModNoop(MQ.OMEGA, index, Q);
                }
                Pow(MQ.OMEGA, index) % Q;
                MQP.mqpow(MQ.OMEGA, index);
            }
        }
    }
    
    function poly_mod_product(a: seq<nat>, b: seq<nat>): (p: seq<nat>)
        requires buff_is_n_elems(a)
        requires buff_is_n_elems(b)
    {
        MQP.poly_mod(
            MQP.poly_mul(buff_as_n_elems(a), buff_as_n_elems(b)),
            MQP.n_ideal())
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

        requires buff_is_n_elems(p0);
        requires buff_is_n_elems(p1);
        requires buff_is_n_elems(p2);
        requires buff_is_n_elems(p3);
        requires buff_is_n_elems(p4);

        requires forward_ntt_eval_all(a1, a0);
        requires forward_ntt_eval_all(b1, b0);
        requires mq_ntt_poly_mul_inv(p0, a1, b1, N.full);
        requires is_bit_rev_shuffle(p0, p1, N);
        requires is_bit_rev_shuffle(p0, p1, N);

        requires inverse_ntt_eval_all(p2, p1);
        requires is_bit_rev_shuffle(p2, p3, N);

        requires mq_poly_scale_inv(p4, p3, MQP.inverse_ntt_scaling_table(), N.full);

        ensures p4 == poly_mod_product(a0, b0)
        // MQP.poly_mod_equiv(p4, MQP.poly_mul(a0, b0), MQP.n_ideal());
    {
        forward_ntt_lemma(a1, a0);
        forward_ntt_lemma(b1, b0);

        var a_hat := MQP.scaled_coeff(buff_as_n_elems(a0));
        var b_hat := MQP.scaled_coeff(buff_as_n_elems(b0));

        forall i | 0 <= i < N.full
            ensures var x := MQP.mqpow(MQ.OMEGA, bit_rev_int(i, N));
                MQP.mqmul(MQP.poly_eval(a_hat, x), MQP.poly_eval(b_hat, x)) == p0[i];
        {
        }

        forall i | 0 <= i < N.full
            ensures var x := MQP.mqpow(MQ.OMEGA, i);
                MQP.mqmul(MQP.poly_eval(a_hat, x), MQP.poly_eval(b_hat, x)) == p1[i];
        {
            reveal is_bit_rev_shuffle();
            bit_rev_symmetric(i, N);
            assert p1[i] == p0[bit_rev_int(i, N)];
        }

        assert p1 == MQP.circle_product(MQP.NTT(MQP.scaled_coeff(a0)), 
            MQP.NTT(MQP.scaled_coeff(b0)));

        forall i | 0 <= i < N.full
            ensures var x := MQP.mqpow(MQ.OMEGA_INV, bit_rev_int(i, N));
                MQP.poly_eval(p1, x) == p2[i];
        {
            reveal CPV.points_eval_suffix_inv();
            assert bit_rev_int(i, N) * 1 == bit_rev_int(i, N);
        }

        forall i | 0 <= i < N.full
            ensures var x := MQP.mqpow(MQ.OMEGA_INV, i);
                MQP.poly_eval(p1, x) == p3[i];
        {
            reveal is_bit_rev_shuffle();
            bit_rev_symmetric(i, N);
            assert p3[i] == p2[bit_rev_int(i, N)];
        }

        var inverse := MQP.INTT(p1);

        var N_INV := MQ.N_INV;
        var PSI_INV := MQ.PSI_INV;
        var R_INV := MQ.R_INV;

        forall i | 0 <= i < N.full
            ensures inverse[i] == (p3[i] * N_INV) % Q

        forall i | 0 <= i < N.full
            ensures p4[i] == (inverse[i] * MQP.mqpow(PSI_INV, i)) % Q;
        {
            MQP.inverse_ntt_scaling_table_axiom(i);
            var t := MQP.mqpow(PSI_INV, i);
            var t0 := (t * N_INV) % Q;
            var t1 := (t0 * R) % Q;
            var t2 := inverse[i];
            assert p4[i] == (p3[i] * t1 * R_INV) % Q;

            gbassert IsModEquivalent(p4[i], t2 * t, Q) by {
                assert IsModEquivalent(R * R_INV, 1, Q) by {
                    MQ.Nth_root_lemma();
                }
                assert IsModEquivalent(t0, t * N_INV, Q);
                assert IsModEquivalent(t1, t0 * R, Q);
                assert IsModEquivalent(t2, p3[i] * N_INV, Q);
                assert IsModEquivalent(p4[i], p3[i] * t1 * R_INV, Q);
            }
        }

        assert p4 == MQP.negatively_wrapped_convolution(a0, b0);
        MQP.negatively_wrapped_convolution_lemma(a0, b0, p4);
    }

    predicate poly_sub_loop_inv(f_new: seq<nat>, f: seq<nat>, g: seq<nat>, i: nat)
    {
        reveal buff_is_n_elems();
        && buff_is_n_elems(f_new)
        && buff_is_n_elems(f)
        && buff_is_n_elems(g)
        && 0 <= i <= N.full
        && f_new[i..] == f[i..]
        && (forall j | 0 <= j < i :: f_new[j] == MQP.mqsub(f[j], g[j]))
    }

    lemma poly_sub_loop_correct(f_new: seq<nat>, f_old: seq<nat>, f_orig:seq<nat>, g: seq<nat>, i: nat)
        requires i < N.full;
        requires poly_sub_loop_inv(f_old, f_orig, g, i)
        requires f_new == f_old[i := MQP.mqsub(f_orig[i], g[i])];
        ensures poly_sub_loop_inv(f_new, f_orig, g, i+1);
    {
        assert |f_new| == |f_old|;
        forall j | 0 <= j < |f_new|
            ensures j != i ==> f_new[j] == f_old[j];
            ensures j == i ==> f_new[j] == MQP.mqsub(f_orig[j], g[j]);
    }
}
