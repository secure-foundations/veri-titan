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

// intt wraps

    type iloop_view = INTT.loop_view

    function build_iloop_view(s: elems, d: pow2_t): iloop_view
        requires INTT.build_loop_view.requires(s, d)
    {
        INTT.build_loop_view(s, d)
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
}