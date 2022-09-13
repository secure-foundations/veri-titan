include "../spec/bvop/bv_op.s.dfy"
include "../spec/crypto/falcon512.i.dfy"

abstract module generic_falcon_lemmas {
    import opened Mul
    import opened Power
    import opened DivMod
    import opened integers
    import opened pow2_s

    import opened ntt_index
    import opened falcon_512_i

    import FNTT = falcon_512_i.FNTT
    import INTT = falcon_512_i.INTT

    predicate {:opaque} valid_elems(a: seq<nat>)
        ensures valid_elems(a) ==> |a| == N.full;
    {
        && (|a| == N.full)
        && (forall i | 0 <= i < N.full :: a[i] < Q)
    }

    function {:opaque} as_elems(a: seq<nat>): (a': elems)
        requires valid_elems(a);
        ensures a == a';
    {
        reveal valid_elems();
        a
    }

// mq arith wraps

    function montmul(a: elem, b: elem): elem
    {
        MQP.montmul(a, b)
    }

    function mqadd(a: elem, b: elem): elem
    {
        MQP.mqadd(a, b)
    }

    function mqsub(a: elem, b: elem): elem
    {
        MQP.mqsub(a, b)
    }

    function mqmul(a: elem, b: elem): elem
    {
        MQP.mqmul(a, b)
    }

// table wraps

    function rev_mixed_powers_mont_x_value(i: nat, d: pow2_t): (r: elem)
    {
        FNTT.rev_mixed_powers_mont_x_value(i, d)
    }

    function rev_mixed_powers_mont_table(): elems
    {
        FNTT.rev_mixed_powers_mont_table()
    }

    function rev_omega_inv_powers_x_value(i: nat, d: pow2_t): (r: elem)
    {
        INTT.rev_omega_inv_powers_x_value(i, d)
    }

    function rev_omega_inv_powers_mont_table(): elems
    {
        INTT.rev_omega_inv_powers_mont_table()
    }

    function inverse_ntt_scaling_table(): elems
    {
        MQP.inverse_ntt_scaling_table()
    }

// fntt wraps
    type floop_view = FNTT.loop_view

    function block_size(d: pow2_t): pow2_t
        requires CPV.block_size.requires(d)
    {
        CPV.block_size(d)
    }

    function build_floop_view(s: elems, d: pow2_t): floop_view
        requires FNTT.build_loop_view.requires(s, d)
    {
        FNTT.build_loop_view(s, d)
    }

    function forward_lsize(view: FNTT.loop_view): (r: pow2_t)
        requires view.loop_view_wf();
        ensures r.full <= N.full
    {
        view.lsize()
    }

    predicate forward_ntt_eval_all(a: seq<nat>, coeffs: seq<nat>)
    {
        && valid_elems(a)
        && valid_elems(coeffs)
        && FNTT.ntt_eval_all(as_elems(a), as_elems(coeffs))
    }

    predicate forward_t_loop_inv(a: seq<nat>, d: pow2_t, coeffs: seq<nat>)
        requires 0 <= d.exp <= N.exp;
    {
        && valid_elems(a)
        && valid_elems(coeffs)
        && FNTT.t_loop_inv(as_elems(a), d, as_elems(coeffs))
    }

    predicate forward_s_loop_inv(a: seq<nat>, d: pow2_t, j: nat, bi: nat, view: FNTT.loop_view)
    {
        && valid_elems(a)
        && view.s_loop_inv(as_elems(a), d, j, bi)
    }

    predicate forward_j_loop_inv(a: seq<nat>, d: pow2_t, j: nat, u: nat, view: FNTT.loop_view)
    {
        && valid_elems(a)
        && u == j * (2 * d.full)
        && view.j_loop_inv(as_elems(a), d, j)
    }

    lemma forward_t_loop_inv_pre_lemma(coeffs: seq<nat>)
        requires valid_elems(coeffs);
        ensures N.exp <= N.exp; // ??
        ensures forward_t_loop_inv(coeffs, N, coeffs);
    {
        FNTT.t_loop_inv_pre_lemma(as_elems(coeffs));
    }

    lemma forward_t_loop_inv_post_lemma(a: seq<nat>, one: pow2_t, coeffs: seq<nat>)
        requires one.exp == 0 <= N.exp;
        requires forward_t_loop_inv(a, one, coeffs);
        ensures forward_ntt_eval_all(a, coeffs);
    {
        FNTT.t_loop_inv_post_lemma(a, one, coeffs);
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

    predicate forward_s_loop_update(
        a: seq<nat>,
        a': seq<nat>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: nat,
        o: nat,
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
        && assert valid_elems(a') by {
            reveal valid_elems();
        }
        && view.s_loop_update(as_elems(a), as_elems(a'), d, j, bi)
    }

    lemma forward_s_loop_inv_peri_lemma(a: seq<nat>,
        a': seq<nat>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: nat,
        o: nat,
        view: FNTT.loop_view)

        requires forward_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        requires forward_s_loop_update(a, a', d, j, bi, s, e, o, view);
        ensures forward_s_loop_inv(a', d, j, bi+1, view);
    {
        view.s_loop_inv_peri_lemma(a, a', d, j, bi);
        assert valid_elems(a') by {
            reveal valid_elems();
        }
    }

// intt wraps

    type iloop_view = INTT.loop_view

    function build_iloop_view(s: elems, d: pow2_t): iloop_view
        requires INTT.build_loop_view.requires(s, d)
    {
        INTT.build_loop_view(s, d)
    }

    function inverse_lsize(view: INTT.loop_view): (r: pow2_t)
        requires view.loop_view_wf();
        ensures r.full <= N.full
    {
        view.lsize()
    }

    predicate inverse_ntt_eval_all(a: seq<nat>, coeffs: seq<nat>)
    {
        && valid_elems(a)
        && valid_elems(coeffs)
        && INTT.ntt_eval_all(as_elems(a), as_elems(coeffs))
    }

    predicate inverse_t_loop_inv(a: seq<nat>, d: pow2_t, coeffs: seq<nat>)
        requires 0 <= d.exp <= N.exp;
    {
        && valid_elems(a)
        && valid_elems(coeffs)
        && INTT.t_loop_inv(as_elems(a), d, as_elems(coeffs))
    }

    predicate inverse_s_loop_inv(a: seq<nat>, d: pow2_t, j: nat, bi: nat, view: INTT.loop_view)
    {
        && valid_elems(a)
        && view.s_loop_inv(as_elems(a), d, j, bi)
    }

    predicate inverse_j_loop_inv(a: seq<nat>, d: pow2_t, j: nat, u: nat, view: INTT.loop_view)
    {
        && valid_elems(a)
        && u == j * (2 * d.full)
        && view.j_loop_inv(as_elems(a), d, j)
    }

    lemma inverse_t_loop_inv_pre_lemma(coeffs: seq<nat>)
        requires valid_elems(coeffs);
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

    predicate inverse_s_loop_update(
        a: seq<nat>,
        a': seq<nat>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: nat,
        o: nat,
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
        && assert valid_elems(a') by {
            reveal valid_elems();
        }
        && view.s_loop_update(as_elems(a), as_elems(a'), d, j, bi)
    }

    lemma inverse_s_loop_inv_peri_lemma(a: seq<nat>,
        a': seq<nat>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: nat,
        o: nat,
        view: INTT.loop_view)

        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        requires inverse_s_loop_update(a, a', d, j, bi, s, e, o, view);
        ensures inverse_s_loop_inv(a', d, j, bi+1, view);
    {
        view.s_loop_inv_peri_lemma(a, a', d, j, bi);
        assert valid_elems(a') by {
            reveal valid_elems();
        }
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

// circle product wrap

    predicate circle_product_inv(a: seq<nat>, init_a: seq<nat>, b: seq<nat>, i: nat)
    {
        && valid_elems(a)
        && valid_elems(init_a)
        && valid_elems(b)
        && i <= |init_a| == |a| == |b| == N.full
        && init_a[i..] == a[i..]
        && reveal valid_elems();
        && (forall j: nat | 0 <= j < i :: a[j] == MQP.mqmul(init_a[j], b[j]))
    }

    lemma circle_product_inv_peri_lemma(
        a: seq<nat>, 
        init_a: seq<nat>,
        b: seq<nat>,
        i: nat)
        returns (ai: elem)

        requires i < N.full;
        requires circle_product_inv(a, init_a, b, i);
        ensures init_a[i] < Q;
        ensures b[i] < Q;
        ensures ai == montmul(montmul(init_a[i], b[i]), 10952);
        ensures circle_product_inv(a[i := ai], init_a, b, i+1);
    {
        reveal valid_elems();
        ai := montmul(montmul(init_a[i], b[i]), 10952);
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

// bit rev wraps

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

// polysub wraps

    function bit_rev_view_init(a: seq<nat>): (view: rev_view)
        requires |a| == N.full;
        ensures view.len == N;
        ensures view.shuffle_inv(a);
    {
        var view := rev_view.init_rev_view(a, N);
        view.shuffle_inv_pre_lemma(a, N);
        view
    }

    predicate poly_sub_loop_inv(diff: seq<nat>, f: seq<nat>, g: seq<nat>, i: nat)
    {
        reveal valid_elems();
        && valid_elems(diff)
        && valid_elems(f)
        && valid_elems(g)
        && 0 <= i <= N.full
        && diff[i..] == f[i..]
        && (forall j | 0 <= j < i :: diff[j] == MQP.mqsub(f[j], g[j]))
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
        {}
    }

    lemma bit_rev_view_inv_peri_lemma(
        a: seq<nat>,
        next_b: seq<nat>,
        view: rev_view,
        table: seq<nat>)
        returns (next_view: rev_view)

        requires valid_elems(view.b);
        requires |a| == N.full;
        requires bit_rev_ftable_wf(table);
        requires view.len == N;
        requires view.shuffle_inv(a);
        requires next_b == view.next_rev_buffer();

        requires 2 * view.ti < |init_unfinished(N)|;
        ensures next_view == view.next_rev_view(a);
        ensures next_view.shuffle_inv(a);
        ensures next_view.b == next_b;
        ensures valid_elems(next_view.b);
    {
        next_view := view.next_rev_view(a);
        view.shuffle_inv_peri_lemma(a, next_view);
        reveal valid_elems();
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

    predicate mq_poly_scale_inv(a: seq<nat>, init_a: seq<nat>, b: seq<nat>, i: nat)
    {
        && valid_elems(a)
        && valid_elems(init_a)
        && valid_elems(b)
        && reveal valid_elems();
        && i <= |init_a| == |a| == |b| == N.full
        && init_a[i..] == a[i..]
        && (forall j: nat | 0 <= j < i ::
            a[j] == MQP.montmul(init_a[j], b[j]))
    }

    lemma mq_poly_scale_peri_lemma(
        a: seq<nat>, 
        init_a: seq<nat>,
        b: seq<nat>,
        i: nat)
        returns (ai: elem)

        requires i < N.full;
        requires mq_poly_scale_inv(a, init_a, b, i);
        ensures init_a[i] < Q;
        ensures b[i] < Q;
        ensures ai == MQP.montmul(init_a[i], b[i]);
        ensures mq_poly_scale_inv(a[i := ai], init_a, b, i+1);
    {
        reveal valid_elems();
        ai := MQP.montmul(init_a[i], b[i]);
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

    lemma mq_poly_mod_product_lemma(
        a0: seq<nat>, a1: seq<nat>, b0: seq<nat>, b1: seq<nat>,
        p0: seq<nat>, p1: seq<nat>, p2: seq<nat>, p3: seq<nat>, p4: seq<nat>)

        requires forward_ntt_eval_all(a1, a0);
        requires forward_ntt_eval_all(b1, b0);
        requires circle_product_inv(p0, a1, b1, N.full);
        requires is_bit_rev_shuffle(p0, p1, N);
        requires inverse_ntt_eval_all(p2, p1);
        requires is_bit_rev_shuffle(p2, p3, N);
        requires mq_poly_scale_inv(
            p4, p3, MQP.inverse_ntt_scaling_table(), N.full);
        ensures as_elems(p4) == poly_mod_product(as_elems(a0), as_elems(b0));
    {
        reveal valid_elems();
        poly_mod_product_lemma(a0, a1, b0, b1, p0, p1, p2, p3, p4);
    }
}