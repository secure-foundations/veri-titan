include "../../arch/riscv/machine.s.dfy"
include "../../arch/riscv/vale.i.dfy"
include "ct_std2rev_model.dfy"
include "../bv32_ops.dfy"

include "mq_arith_lemmas.dfy"
include "../DivModNeg.dfy"

module bv32_falcon_lemmas {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul
    import opened DivModNeg
    import opened integers
    import opened bv32_ops
    import opened rv_machine
    import opened rv_vale
    import opened mem
    import flat

    import opened pows_of_2
    import opened ntt_index
    import opened ntt_512_params
    import opened mq_polys
    import opened poly_view
    import opened nth_root
    import opened mq_arith_lemmas
    import forward_ntt
    import inverse_ntt

    lemma {:axiom} rs1_is_half(a: uint32)
        ensures uint32_rs(a, 1) == a / 2;

    lemma {:axiom} ls1_is_double(a: uint32)
        requires a < BASE_31;
        ensures uint32_ls(a, 1) == a * 2;

    predicate {:opaque} buff_is_nsized(a: seq<nat>)
        ensures buff_is_nsized(a) ==> |a| == N.full;
    {
        && (|a| == N.full)
        && (forall i | 0 <= i < N.full :: a[i] < Q)
    }

    predicate fvar_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(iter, heap, if address >= 0 then address else iter.cur_ptr())
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && buff_is_nsized(iter.buff)
    }

    function {:opaque} buff_as_nsized(a: seq<uint16>): (a': n_sized)
        requires buff_is_nsized(a);
        ensures a == a';
    {
        reveal buff_is_nsized();
        a
    }

    function forward_lsize(view: forward_ntt.loop_view): (r: pow2_t)
        requires view.loop_view_wf();
        ensures r.full <= N.full
    {
        view.lsize()
    }

    predicate forward_ntt_eval_all(a: seq<uint16>, coeffs: seq<uint16>)
    {
        && buff_is_nsized(a)
        && buff_is_nsized(coeffs)
        && forward_ntt.ntt_eval_all(buff_as_nsized(a), buff_as_nsized(coeffs))
    }

    predicate forward_t_loop_inv(a: seq<uint16>, d: pow2_t, coeffs: seq<uint16>)
        requires 0 <= d.exp <= N.exp;
    {
        && buff_is_nsized(a)
        && buff_is_nsized(coeffs)
        && forward_ntt.t_loop_inv(buff_as_nsized(a), d, buff_as_nsized(coeffs))
    }

    lemma forward_t_loop_inv_pre_lemma(coeffs: seq<uint16>)
        requires buff_is_nsized(coeffs);
        ensures N.exp <= N.exp; // ??
        ensures forward_t_loop_inv(coeffs, N, coeffs);
    {
        forward_ntt.t_loop_inv_pre_lemma(buff_as_nsized(coeffs));
    }

    lemma forward_t_loop_inv_post_lemma(a: seq<uint16>, one: pow2_t, coeffs: seq<uint16>)
        requires one.exp == 0 <= N.exp;
        requires forward_t_loop_inv(a, one, coeffs);
        ensures forward_ntt_eval_all(a, coeffs);
    {
        forward_ntt.t_loop_inv_post_lemma(a, one, coeffs);
    }

    predicate forward_s_loop_inv(a: seq<uint16>, d: pow2_t, j: nat, bi: nat, view: forward_ntt.loop_view)
    {
        && buff_is_nsized(a)
        && view.s_loop_inv(buff_as_nsized(a), d, j, bi)
    }

    lemma forward_s_loop_inv_pre_lemma(
        a: seq<uint16>,
        d: pow2_t,
        j: nat,
        t: pow2_t,
        u: nat,
        ot3: uint32,
        t3: uint32,
        t6: uint32,
        s5: uint32,
        view: forward_ntt.loop_view)

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
        ensures rev_mixed_powers_mont_table()[t.full + j] == 
            mqmul(rev_mixed_powers_mont_x_value(2 * j, d), R);
    {
        view.s_loop_inv_pre_lemma(buff_as_nsized(a), d, j);
        rev_mixed_powers_mont_table_lemma(t, d, j);
        assert uint32_add(t.full, j) == t.full + j;
        ls1_is_double(t.full + j);
        rev_mixed_powers_mont_table_lemma(t, d, j);

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

    lemma forward_s_loop_inv_post_lemma(
        a: seq<uint16>,
        d: pow2_t,
        j: nat,
        u: uint32,
        bi: nat,
        ot3: uint32,
        t3: uint32,
        t6: uint32,
        view: forward_ntt.loop_view)
    
        requires bi == d.full;
        requires t6 == 2 * d.full;
        requires u == j * (2 * d.full);
        requires forward_s_loop_inv(a, d, j, bi, view);
        requires ot3 == 2 * u + 2 * d.full;
        requires t3 == uint32_add(ot3, t6);
        ensures t3 == 2 * (u + 2 * d.full);
        ensures forward_j_loop_inv(a, d, j + 1, u + 2 * d.full, view);
    {
        view.s_loop_inv_post_lemma(buff_as_nsized(a), d, j, bi);

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
        a: seq<uint16>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s4: uint32,
        s2: uint32,
        t4: uint32,
        t5: uint32,
        t6: uint32,
        view: forward_ntt.loop_view)
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
        ensures a[s] == level_points_view(a, view.hsize)[bi][2*j];
        ensures s == point_view_index(bi, 2*j, view.hsize);
        ensures a[s+d.full] == level_points_view(a, view.hsize)[bi][2*j+1];
        ensures s+d.full == point_view_index(bi, 2*j+1, view.hsize);
    {
        s := view.higher_points_view_index_lemma(buff_as_nsized(a), d, j, bi);
        assert 2 * (bi + (2*j) * d.full) == 2 * bi + 2 * (j * (2 * d.full)) by {
            LemmaMulProperties();
        }
    }

    predicate forward_s_loop_update(
        a: seq<uint16>,
        a': seq<uint16>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: uint32,
        o: uint32,
        view: forward_ntt.loop_view)

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
        && assert buff_is_nsized(a') by {
            reveal buff_is_nsized();
        }
        && view.s_loop_update(buff_as_nsized(a), buff_as_nsized(a'), d, j, bi)
    }

    lemma forward_s_loop_inv_peri_lemma(a: seq<uint16>,
        a': seq<uint16>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: uint32,
        o: uint32,
        view: forward_ntt.loop_view)

        requires forward_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        requires forward_s_loop_update(a, a', d, j, bi, s, e, o, view);
        ensures forward_s_loop_inv(a', d, j, bi+1, view);
    {
        view.s_loop_inv_peri_lemma(a, a', d, j, bi);
        assert buff_is_nsized(a') by {
            reveal buff_is_nsized();
        }
    }

    lemma forward_higher_points_view_index_lemma(a: seq<uint16>, d: pow2_t, j: nat, bi: nat, view: forward_ntt.loop_view)
        returns (s: nat)
    
        requires forward_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        ensures s == bi + (2*j) * d.full;
        ensures s + d.full < N.full;
        ensures a[s] ==
            level_points_view(buff_as_nsized(a), view.hsize)[bi][2*j];
        ensures s == point_view_index(bi, 2*j, view.hsize);
        ensures a[s+d.full] ==
            level_points_view(buff_as_nsized(a), view.hsize)[bi][2*j+1];
        ensures s+d.full == point_view_index(bi, 2*j+1, view.hsize);
    {
        s := view.higher_points_view_index_lemma(buff_as_nsized(a), d, j, bi);
    }

    predicate forward_j_loop_inv(a: seq<uint16>, d: pow2_t, j: nat, u: nat, view: forward_ntt.loop_view)
    {
        && buff_is_nsized(a)
        && u == j * (2 * d.full)
        && view.j_loop_inv(buff_as_nsized(a), d, j)
    }

    lemma forward_j_loop_inv_pre_lemma(a: seq<uint16>, d: pow2_t, view: forward_ntt.loop_view)
        requires 0 <= d.exp < N.exp;
        requires forward_t_loop_inv(a, pow2_double(d), view.coefficients);
        requires view.loop_view_wf();
        requires view.hsize == block_size(d);
        ensures forward_j_loop_inv(a, d, 0, 0, view);
    {
        view.j_loop_inv_pre_lemma(buff_as_nsized(a), d);
    }

    lemma forward_j_loop_inv_post_lemma(a: seq<uint16>, d: pow2_t, j: nat, u: nat, view: forward_ntt.loop_view)
        requires forward_j_loop_inv(a, d, j, u, view);
        requires j == view.lsize().full;
        requires 0 <= view.hsize.exp <= N.exp;
        requires view.hsize == block_size(d);
        ensures forward_ntt.t_loop_inv(a, d, view.coefficients);
    {
        view.j_loop_inv_post_lemma(a, d, j);
    }

    function inverse_lsize(view: inverse_ntt.loop_view): (r: pow2_t)
        requires view.loop_view_wf();
        ensures r.full <= N.full
    {
        view.lsize()
    }

    predicate inverse_ntt_eval_all(a: seq<uint16>, coeffs: seq<uint16>)
    {
        && buff_is_nsized(a)
        && buff_is_nsized(coeffs)
        && inverse_ntt.ntt_eval_all(buff_as_nsized(a), buff_as_nsized(coeffs))
    }

    predicate inverse_t_loop_inv(a: seq<uint16>, d: pow2_t, coeffs: seq<uint16>)
        requires 0 <= d.exp <= N.exp;
    {
        && buff_is_nsized(a)
        && buff_is_nsized(coeffs)
        && inverse_ntt.t_loop_inv(buff_as_nsized(a), d, buff_as_nsized(coeffs))
    }

    lemma inverse_t_loop_inv_pre_lemma(coeffs: seq<uint16>)
        requires buff_is_nsized(coeffs);
        ensures N.exp <= N.exp; // ??
        ensures inverse_t_loop_inv(coeffs, N, coeffs);
    {
        inverse_ntt.t_loop_inv_pre_lemma(buff_as_nsized(coeffs));
    }

    lemma inverse_t_loop_inv_post_lemma(a: seq<uint16>, one: pow2_t, coeffs: seq<uint16>)
        requires one.exp == 0 <= N.exp;
        requires inverse_t_loop_inv(a, one, coeffs);
        ensures inverse_ntt_eval_all(a, coeffs);
    {
        inverse_ntt.t_loop_inv_post_lemma(a, one, coeffs);
    }

    predicate inverse_s_loop_inv(a: seq<uint16>, d: pow2_t, j: nat, bi: nat, view: inverse_ntt.loop_view)
    {
        && buff_is_nsized(a)
        && view.s_loop_inv(buff_as_nsized(a), d, j, bi)
    }

    lemma inverse_s_loop_inv_pre_lemma(
        a: seq<uint16>,
        d: pow2_t,
        j: nat,
        t: pow2_t,
        u: nat,
        ot3: uint32,
        t3: uint32,
        t6: uint32,
        s5: uint32,
        view: inverse_ntt.loop_view)


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
        ensures rev_omega_inv_powers_mont_table()[t.full + j] == 
            mqmul(rev_omega_inv_powers_x_value(2 * j, d), R);
    {
        view.s_loop_inv_pre_lemma(buff_as_nsized(a), d, j);
        rev_omega_inv_powers_mont_table_lemma(t, d, j);
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
        a: seq<uint16>,
        d: pow2_t,
        j: nat,
        u: uint32,
        bi: nat,
        ot3: uint32,
        t3: uint32,
        t6: uint32,
        view: inverse_ntt.loop_view)
    

        requires bi == d.full;
        requires t6 == 2 * d.full;
        requires u == j * (2 * d.full);
        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires ot3 == 2 * u + 2 * d.full;
        requires t3 == uint32_add(ot3, t6);
        ensures t3 == 2 * (u + 2 * d.full);
        ensures inverse_j_loop_inv(a, d, j + 1, u + 2 * d.full, view);
    {
        view.s_loop_inv_post_lemma(buff_as_nsized(a), d, j, bi);

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
        a: seq<uint16>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s4: uint32,
        s2: uint32,
        t4: uint32,
        t5: uint32,
        t6: uint32,
        view: inverse_ntt.loop_view)
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
        ensures a[s] == level_points_view(a, view.hsize)[bi][2*j];
        ensures s == point_view_index(bi, 2*j, view.hsize);
        ensures a[s+d.full] == level_points_view(a, view.hsize)[bi][2*j+1];
        ensures s+d.full == point_view_index(bi, 2*j+1, view.hsize);
    {
        s := view.higher_points_view_index_lemma(buff_as_nsized(a), d, j, bi);
        assert 2 * (bi + (2*j) * d.full) == 2 * bi + 2 * (j * (2 * d.full)) by {
            LemmaMulProperties();
        }
    }

    predicate inverse_s_loop_update(
        a: seq<uint16>,
        a': seq<uint16>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: uint32,
        o: uint32,
        view: inverse_ntt.loop_view)

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
        && assert buff_is_nsized(a') by {
            reveal buff_is_nsized();
        }
        && view.s_loop_update(buff_as_nsized(a), buff_as_nsized(a'), d, j, bi)
    }

    lemma inverse_s_loop_inv_peri_lemma(a: seq<uint16>,
        a': seq<uint16>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: uint32,
        o: uint32,
        view: inverse_ntt.loop_view)

        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        requires inverse_s_loop_update(a, a', d, j, bi, s, e, o, view);
        ensures inverse_s_loop_inv(a', d, j, bi+1, view);
    {
        view.s_loop_inv_peri_lemma(a, a', d, j, bi);
        assert buff_is_nsized(a') by {
            reveal buff_is_nsized();
        }
    }

    lemma inverse_higher_points_view_index_lemma(a: seq<uint16>, d: pow2_t, j: nat, bi: nat, view: inverse_ntt.loop_view)
        returns (s: nat)
    
        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        ensures s == bi + (2*j) * d.full;
        ensures s + d.full < N.full;
        ensures a[s] ==
            level_points_view(buff_as_nsized(a), view.hsize)[bi][2*j];
        ensures s == point_view_index(bi, 2*j, view.hsize);
        ensures a[s+d.full] ==
            level_points_view(buff_as_nsized(a), view.hsize)[bi][2*j+1];
        ensures s+d.full == point_view_index(bi, 2*j+1, view.hsize);
    {
        s := view.higher_points_view_index_lemma(buff_as_nsized(a), d, j, bi);
    }

    predicate inverse_j_loop_inv(a: seq<uint16>, d: pow2_t, j: nat, u: nat, view: inverse_ntt.loop_view)
    {
        && buff_is_nsized(a)
        && u == j * (2 * d.full)
        && view.j_loop_inv(buff_as_nsized(a), d, j)
    }

    lemma inverse_j_loop_inv_pre_lemma(a: seq<uint16>, d: pow2_t, view: inverse_ntt.loop_view)
        requires 0 <= d.exp < N.exp;
        requires inverse_t_loop_inv(a, pow2_double(d), view.coefficients);
        requires view.loop_view_wf();
        requires view.hsize == block_size(d);
        ensures inverse_j_loop_inv(a, d, 0, 0, view);
    {
        view.j_loop_inv_pre_lemma(buff_as_nsized(a), d);
    }

    lemma inverse_j_loop_inv_post_lemma(a: seq<uint16>, d: pow2_t, j: nat, u: nat, view: inverse_ntt.loop_view)
        requires inverse_j_loop_inv(a, d, j, u, view);
        requires j == view.lsize().full;
        requires 0 <= view.hsize.exp <= N.exp;
        requires view.hsize == block_size(d);
        ensures inverse_ntt.t_loop_inv(a, d, view.coefficients);
    {
        view.j_loop_inv_post_lemma(a, d, j);
    }

    function bit_rev_view_init(a: seq<uint16>): (view: rev_view)

        requires |a| == N.full;
        ensures view.len == N;
        ensures view.shuffle_inv(a);
    {
        var view := rev_view.init_rev_view(a, N);
        view.shuffle_inv_pre_lemma(a, N);
        view
    }

    function {:opaque} ftable_cast(ftable: seq<uint16>): (r: seq<(nat, nat)>)

        requires |ftable| == |init_unfinished(N)|;
        ensures |r| == |init_unfinished(N)| / 2;
    {
        var size := |init_unfinished(N)| / 2;
        seq(size, i requires 0 <= i < size => (ftable[2 * i], ftable[2 * i + 1]))
    }

    // lemma ftable_index_lemma(a: seq<uint16>, ftable: seq<uint16>, table: seq<(nat, nat)>, ti: nat)
    //     requires N == pow2_t_cons(512, 9);
    //     requires |ftable| == |init_unfinished(N)|;
    //     requires ftable_cast(ftable) == table;
    //     requires 0 <= 2 * ti + 1 < |ftable|;
    //     requires |a| == N.full;
    //     requires table_wf(table, a, N);
    //     ensures ti < |table|;
    //     ensures ftable[2 * ti] == build_view(a, ti, N).get_split_index();
    //     ensures ftable[2 * ti + 1] == bit_rev_int(ftable[2 * ti], N);
    // {

    // }

    predicate bit_rev_ftable_wf(ftable: seq<uint16>)

    {
        && |ftable| == |init_unfinished(N)|
        && table_wf(ftable_cast(ftable), N)
    }

    predicate bit_rev_shuffle_inv(a: seq<uint16>, view: rev_view)
        requires |a| == view.len.full;
    {
       view.shuffle_inv(a)
    }

    lemma bit_rev_index_lemma(
        a: seq<uint16>,
        ftable: seq<uint16>,
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
        }

        // ftable_index_lemma(a, ftable, table, ti);
        assert sbi == build_view(a, ti, N).get_split_index();
        assert rsbi == bit_rev_int(ftable[2 * ti], N);

        ls1_is_double(sbi);
        ls1_is_double(rsbi);
    }

    lemma bit_rev_view_inv_peri_lemma(
        a: seq<uint16>,
        next_b: seq<uint16>,
        view: rev_view,
        table: seq<uint16>)
        returns (next_view: rev_view)
        

        requires buff_is_nsized(view.b);
        requires |a| == N.full;
        requires bit_rev_ftable_wf(table);
        requires view.len == N;
        requires view.shuffle_inv(a);
        requires next_b == view.next_rev_buffer();

        requires 2 * view.ti < |init_unfinished(N)|;
        ensures next_view == view.next_rev_view(a);
        ensures next_view.shuffle_inv(a);
        ensures next_view.b == next_b;
        ensures buff_is_nsized(next_view.b);
    {
        next_view := view.next_rev_view(a);
        view.shuffle_inv_peri_lemma(a, next_view);
        reveal buff_is_nsized();
    }

    lemma bit_rev_view_inv_post_lemma(a: seq<uint16>, view: rev_view)

        requires |a| == N.full;
        requires view.len == N;
        requires view.shuffle_inv(a);
        requires 2 * view.ti == |init_unfinished(N)|; 
        ensures is_bit_rev_shuffle(a, view.b, N);
    {
        view.shuffle_inv_post_lemma(a);
    }

    predicate mq_ntt_poly_mul_inv(a: seq<uint16>, init_a: seq<uint16>, b: seq<uint16>, i: nat)
    {
        && buff_is_nsized(init_a)
        && buff_is_nsized(b)
        && i <= |init_a| == |a| == |b| == N.full
        && init_a[i..] == a[i..]
        && reveal buff_is_nsized();
        && (forall j: nat | 0 <= j < i :: a[j] == mqmul(init_a[j], b[j]))
    }
    
    lemma mq_ntt_poly_mul_inv_peri_lemma(
        a: seq<uint16>, 
        init_a: seq<uint16>,
        ai: uint32,
        b: seq<uint16>,
        i: nat)

        requires i < N.full;
        requires mq_ntt_poly_mul_inv(a, init_a, b, i);
        requires init_a[i] < Q;
        requires b[i] < Q;
        requires ai == montmul(montmul(init_a[i], 10952), b[i]);
        ensures  mq_ntt_poly_mul_inv(a[i := ai], init_a, b, i+1);
    {
        var next_a := a[i := ai];
        forall j: nat | 0 <= j < i+1
            ensures next_a[j] == mqmul(init_a[j], b[j])
        {
            if j != i {
                assert next_a[j] == a[j];
            } else {
                assert next_a[j] == ai;
                assume ai == mqmul(init_a[j], b[j]);
            }
        }
    }

    predicate mq_poly_scale_inv(a: seq<uint16>, init_a: seq<uint16>, b: seq<uint16>, i: nat)

    {
        && buff_is_nsized(init_a)
        && buff_is_nsized(b)
        && reveal buff_is_nsized();
        && i <= |init_a| == |a| == |b| == N.full
        && init_a[i..] == a[i..]
        && (forall j: nat | 0 <= j < i :: a[j] == montmul(init_a[j], b[j]))
    }

    lemma mq_poly_scale_peri_lemma(
        a: seq<uint16>, 
        init_a: seq<uint16>,
        ai: uint32,
        b: seq<uint16>,
        i: nat)

        requires i < N.full;
        requires mq_poly_scale_inv(a, init_a, b, i);
        requires init_a[i] < Q;
        requires b[i] < Q;
        requires ai == montmul(init_a[i], b[i]);
        ensures  mq_poly_scale_inv(a[i := ai], init_a, b, i+1);
    {
        var next_a := a[i := ai];
        forall j: nat | 0 <= j < i+1
            ensures next_a[j] == montmul(init_a[j], b[j])
        {
            if j != i {
                assert next_a[j] == a[j];
            } else {
                assert next_a[j] == ai;
            }
        }
    }

    lemma mq_ntt_mul_lemma(
        a0: seq<uint16>,
        a1: seq<uint16>,
        b0: seq<uint16>,
        b1: seq<uint16>,
        p0: seq<uint16>,
        p1: seq<uint16>,
        p2: seq<uint16>,
        p3: seq<uint16>,
        p4: seq<uint16>)

        requires buff_is_nsized(a0);
        requires buff_is_nsized(a1);
        requires buff_is_nsized(b0);
        requires buff_is_nsized(b1);
        requires buff_is_nsized(p0);
        requires buff_is_nsized(p1);
        requires buff_is_nsized(p2);
        requires buff_is_nsized(p3);
        requires buff_is_nsized(p4);

        requires forward_ntt_eval_all(a1, a0);
        requires forward_ntt_eval_all(b1, b0);
        requires mq_ntt_poly_mul_inv(p0, a1, b1, N.full);
        requires is_bit_rev_shuffle(p0, p1, N);
        requires is_bit_rev_shuffle(p0, p1, N);

        requires inverse_ntt_eval_all(p2, p1);
        requires is_bit_rev_shuffle(p2, p3, N);

        requires mq_poly_scale_inv(p4, p3, inverse_ntt_scaling_table(), N.full);

        ensures poly_mod_equiv(p4, poly_mul(a0, b0), n_ideal());
    {
        forall i | 0 <= i < N.full
            ensures var x := mqpow(PSI, 2 * bit_rev_int(i, N) + 1);
                mqmul(poly_eval(a0, x), poly_eval(b0, x)) == p0[i];
        {
            reveal points_eval_suffix_inv();
            assert 2 * bit_rev_int(i, N) * 1 == 2 * bit_rev_int(i, N);
        }

        forall i | 0 <= i < N.full
            ensures var x := mqpow(PSI, 2 * i + 1);
                mqmul(poly_eval(a0, x), poly_eval(b0, x)) == p1[i];
        {
            reveal is_bit_rev_shuffle();
            bit_rev_symmetric(i, N);
            assert p1[i] == p0[bit_rev_int(i, N)];
        }

        forall i | 0 <= i < N.full
            ensures var x := mqpow(OMEGA_INV, bit_rev_int(i, N));
                poly_eval(p1, x) == p2[i];
        {
            reveal points_eval_suffix_inv();
            assert bit_rev_int(i, N) * 1 == bit_rev_int(i, N);
        }

        forall i | 0 <= i < N.full
            ensures var x := mqpow(OMEGA_INV, i);
                poly_eval(p1, x) == p3[i];
        {
            reveal is_bit_rev_shuffle();
            bit_rev_symmetric(i, N);
            assert p3[i] == p2[bit_rev_int(i, N)];
        }

        forall i | 0 <= i < N.full
            ensures
                var x := mqpow(OMEGA_INV, i);
                p4[i] == (poly_eval(p1, x) * mqpow(PSI_INV, i) * N_INV) % Q;
        {
            inverse_ntt_scaling_table_axiom(i);
            assert p4[i] == montmul(p3[i], mqmul(mqmul(mqpow(PSI_INV, i), N_INV), R));
            assume p4[i] == (p3[i] * mqpow(PSI_INV, i) * N_INV) % Q;
        }

        assert p4 == negatively_wrapped_convolution(a0, b0, p1);

        negatively_wrapped_convolution_lemma(a0, b0, p1, p4);
    }

    predicate poly_sub_loop_inv(f_new: seq<uint16>, f: seq<uint16>, g: seq<uint16>, i: nat)
    {
        reveal buff_is_nsized();
        && buff_is_nsized(f_new)
        && buff_is_nsized(f)
        && buff_is_nsized(g)
        && 0 <= i <= N.full
        && f_new[i..] == f[i..]
        && (forall j :: 0 <= j < i ==> f_new[j] == mqsub(f[j], g[j]))
    }

    
  lemma mul_upper_bound_Qsquared(x: nat, y: nat)
    requires x <= 12289;
    requires y <= 12289;
    requires 0 <= x
    requires 0 <= y
    ensures mul(x, y) == x * y;
    ensures x * y <= 151019521;
  {
    reveal dw_lh();
    Mul.LemmaMulNonnegative(x, y);
    Mul.LemmaMulUpperBound(x, 12289, y, 12289);
    DivMod.LemmaSmallMod(x * y, BASE_32);
  }

    lemma poly_sub_loop_correct(f_new: seq<uint16>, f_old: seq<uint16>, f_orig:seq<uint16>, g: seq<uint16>, i: nat)
      requires i < N.full;
      requires poly_sub_loop_inv(f_old, f_orig, g, i)
      requires f_new == f_old[i := mqsub(f_orig[i], g[i])];
      ensures poly_sub_loop_inv(f_new, f_orig, g, i+1);
    {
      assert |f_new| == |f_old|;
      assert (forall j | 0 <= j < |f_new| :: j != i
        ==> f_new[j] == f_old[j] && j == i ==> f_new[j] == mqsub(f_orig[j], g[j]));
    }

    lemma lemma_shiftmul3(a: nat, b: nat, ab: nat, ab3: nat)
        requires a < Q;
        requires b < Q;
        requires ab == uint32_mul(a, b)
        requires ab3 == uint32_add(uint32_ls(ab, 1), ab);
        ensures ab3 == 3 * a * b;
        ensures ab3 == 3 * ab;
        ensures ab == a * b;
        ensures ab < Q * Q;
    {

      reveal dw_lh();
      Mul.LemmaMulNonnegative(a, b);
      Mul.LemmaMulUpperBound(a, Q-1, b, Q-1);
      DivMod.LemmaSmallMod(a * b, BASE_32);

      assert a * b == ab;
      assert ab3 == 3 * ab by { ls1_is_double(ab); }
      assert ab3 == 3 * a * b by { Mul.LemmaMulIsAssociativeAuto(); }
    }

    lemma lemma_Q0Ixy_correct(x: nat, y: nat, xy: uint32, xy3: uint32, Q0Ixy: nat)
      requires x < Q;
      requires y < Q;
      requires xy < Q * Q;
      requires xy as nat == x * y;
      requires xy3 as nat == 3 * x * y;
      requires Q0Ixy == uint32_sub(uint32_ls(xy3, 12), xy);
      ensures IsModEquivalent(Q0Ixy, 12287 * x * y, BASE_32);
    {
      var sh := uint32_ls(xy3, 12);
      assert sh == (xy3 * Power2.Pow2(12)) % BASE_32 by { ls_is_mul_mod_base(xy3, 12); }

      var sh_int := sh as int;
      var xy_int := xy as int;
      
      gbassert IsModEquivalent(Q0Ixy, 12287 * x * y, BASE_32) by {
        assert xy3 == 3 * x * y;
        assert xy_int == x * y;
        assert IsModEquivalent(sh_int, xy3 * 4096, BASE_32) by { Power2.Lemma2To64(); }
        assert IsModEquivalent(Q0Ixy, sh_int - xy_int, BASE_32);
      }
    }

    lemma lemma_shiftadd3(x: uint32, v: uint32, v3: nat)
        requires v == uint32_rs(uint32_ls(x, 16), 16); // < BASE_16 - 1
        requires v3 == uint32_add(uint32_ls(v, 1), v); // < 3 * (BASE_16 - 1)
        ensures v < BASE_16; 
        ensures v3 == 3 * v;
        //ensures IsModEquivalent(v, x, BASE_16);
    {
      var lsx := uint32_ls(x, 16);
      assert lsx == (x * Power2.Pow2(16)) % BASE_32 by { ls_is_mul_mod_base(x, 16); }
      
      assert v == (lsx / Power2.Pow2(16)) % BASE_32 by { rs_is_div_mod_base(lsx, 16); }
      assert v < BASE_32;
      assert v == (lsx / Power2.Pow2(16)) by {
        DivMod.LemmaDivNonincreasing(lsx, Power2.Pow2(16));
        DivMod.LemmaDivPosIsPos(lsx, Power2.Pow2(16));
        DivMod.LemmaSmallMod((lsx / Power2.Pow2(16)), BASE_32);
      }

      assert v < BASE_16 by {
        Power2.Lemma2To64();
        DivMod.LemmaDivIsOrdered(lsx, BASE_32, BASE_16);
      }

      assert v3 == v * 3 by { ls1_is_double(v); }
    }

    lemma lemma_12289(v: uint32, v3: uint32, w: uint32)
      requires v < BASE_16;
      requires v3 == 3 * v;
      requires w == uint32_add(uint32_ls(v3, 12), v);
      ensures w == Q * v;
      ensures w <= Q * (BASE_16 - 1);
    {
      var lsv3 := uint32_ls(v3, 12);
      assert lsv3 == (v3 * Power2.Pow2(12)) % BASE_32 by { ls_is_mul_mod_base(v3, 12); }
      assert lsv3 == (3 * v * Power2.Pow2(12)) % BASE_32 by { Mul.LemmaMulIsAssociativeAuto(); }

      var lsv3_int := lsv3 as int;
      
      gbassert IsModEquivalent(w, 12289 * v, BASE_32) by {
        assert IsModEquivalent(lsv3_int, 3 * v * 4096, BASE_32) by { Power2.Lemma2To64(); }
        assert IsModEquivalent(w, lsv3_int + v, BASE_32);
      }
    }

    lemma lemma_zw_shift(w: uint32, xy: uint32, z:uint32)
      requires w <= Q * (BASE_16 - 1);
      requires xy <= (Q-1) * (Q-1);
      requires z == uint32_rs(uint32_add(w, xy), 16);
      ensures z == uint32_rs(w + xy, 16);
      ensures z < 2 * Q; 
    {
      var wxy := uint32_add(w, xy);
      assert wxy == w + xy;

      assert z == uint32_rs(wxy, 16);
      assert z == (wxy / Power2.Pow2(16)) % BASE_32 by { rs_is_div_mod_base(wxy, 16); }
      
      assert wxy <= Q * (BASE_16 - 1) + (Q-1) * (Q-1);
      assert z == (wxy / Power2.Pow2(16)) by {
        DivMod.LemmaDivNonincreasing(wxy, Power2.Pow2(16));
        DivMod.LemmaDivPosIsPos(wxy, Power2.Pow2(16));
        DivMod.LemmaSmallMod((wxy / Power2.Pow2(16)), BASE_32);
      }
      
      assert z <= (Q * (BASE_16 - 1) + (Q-1) * (Q-1)) / Power2.Pow2(16) by {
        DivMod.LemmaDivIsOrdered(wxy, Q * (BASE_16 - 1) + (Q-1) * (Q-1), Power2.Pow2(16));
      }

      assert z <= 14592 by { Power2.Lemma2To64(); }
      assert 14592 < 2 * Q;
    }
    
     lemma lemma_and_with_constants(x: uint32)
      ensures uint32_and(0, x) == 0;
      ensures uint32_and(0xffff_ffff, x) == x;
     {
      reveal_and();
     }

     lemma lemma_cond_add_Q(z: uint32, d: uint32, b: uint32, c: uint32, r: uint32)
         requires z < 2 * Q;
         requires d == uint32_sub(z, Q);
         requires b == to_uint32(int32_rs(to_int32(d), 31));
         requires c == uint32_and(b, Q);
         requires r == uint32_add(c, d);
         ensures r < Q;
         ensures r == z % Q;
     {

      if to_int32(d) >= 0 {
        assert int32_rs(to_int32(d), 31) == 0 by { lemma_rs_by_31(to_int32(d)); }
        assert uint32_and(0, Q) == 0 by { lemma_and_with_constants(Q); }
        assert IsModEquivalent(r, z, Q);
      }
      else {
        assert int32_rs(to_int32(d), 31) == -1 by { lemma_rs_by_31(to_int32(d)); }
        assert uint32_and(b, Q) == Q by { lemma_and_with_constants(Q); }
        assert IsModEquivalent(r, z, Q);
      }
     }
 
     lemma lemma_montymul_correct(x: nat, y: nat, xy: uint32, v: nat, w: uint32, z: uint32, rr: uint32)
       requires x < Q;
       requires y < Q;
       requires xy == x * y;
       requires v == (12287 * x * y) % BASE_16;
       requires w == Q * v;
       requires w as nat + xy as nat < BASE_32;
       requires z == uint32_rs(w + xy, 16);
       requires z < 2 * Q;
       requires rr == z % Q;
       ensures IsModEquivalent(rr * 4091, x * y, Q); // WTS: rr == x*y/4091 mod Q
     {
      gbassert IsModEquivalent(w + xy, 0, BASE_16) by {
         assert IsModEquivalent(v, 12287 * x * y, BASE_16);
         assert Q == 12289;
         assert BASE_16 == 65536;
         assert w == Q * v;
         assert xy == x * y;
        }

        DivMod.LemmaFundamentalDivMod(w + xy, BASE_16);
        assert (w + xy) == BASE_16 * (w + xy) / BASE_16 + (w + xy) % BASE_16;

        calc {
          w + xy;
          { DivMod.LemmaFundamentalDivMod(w + xy, BASE_16); }
          BASE_16 * (w + xy) / BASE_16 + (w + xy) % BASE_16;
          BASE_16 * (w + xy) / BASE_16;
          BASE_16 * ((w + xy) / BASE_16);
          
          z * BASE_16;
        }

       gbassert IsModEquivalent(rr * 4091, x * y, Q) by {
         assert IsModEquivalent(v, 12287 * x * y, BASE_16);
         assert Q == 12289;
         assert BASE_16 == 65536;
         assert IsModEquivalent(4091, BASE_16, Q);
         assert w == Q * v;
         assert xy == x * y;
         assert z * BASE_16 == (w + xy);
         assert IsModEquivalent(w + xy, 0, BASE_16);
         assert IsModEquivalent(rr, z, Q);
       }
     }
}
