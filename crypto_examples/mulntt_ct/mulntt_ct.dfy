include "mulntt_ct_rec.dfy"

module mulntt_ct {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul

    import opened pows_of_2
    import opened nth_root
    import opened ntt_index

    import opened mulntt_ct_rec
    import opened ntt_polys

    // function method A(): n_sized

    // function method P(): n_sized

    // lemma P_table_index_bounded_lemma(t: pow2_t, j: nat)
    //     requires t.exp < LOGN;
    //     requires j < t.full;
    //     ensures t.full + j < N;
    // {
    //     assume false;
    // }

    method j_loop(a: n_sized, d: pow2_t, j: nat, ghost view: loop_view)
    returns (a': n_sized)

        requires view.j_loop_inv(a, d, j);
        requires j < view.lsize().full;
        ensures view.j_loop_inv(a', d, j + 1);
    {
        view.s_loop_inv_pre_lemma(a, d, j);

        var u := (2 * j) * d.full;
        var w := x_value(2 * j, d); // TODO: read from table
        // P_table_index_bounded_lemma(t, j);
        // var w := P()[t.full + j]; // psi_t * w_t^bitrev(j)

        var s := u;
        a' := a;

        ghost var bi := 0;

        while (s < u + d.full)
            invariant view.s_loop_inv(a', d, j, s-u);
        {
            var a :n_sized := a';
            var bi := s-u;

            var _ := view.higher_points_view_index_lemma(a, d, j, bi);

            var e := a[s];
            var o := a[s + d.full];

            var x := modmul(o, w);
            a' := a[s+d.full := modsub(e, x)];
            a' := a'[s := modadd(e, x)];
            s := s + 1;

            view.s_loop_inv_peri_lemma(a, a', d, j, bi);
        }

        assert s == u + d.full;
        view.s_loop_inv_post_lemma(a', d, j, d.full);
    }

    method t_loop(a: n_sized, t: pow2_t, d: pow2_t, ghost view: loop_view)
        returns (a': n_sized)

        requires view.j_loop_inv(a, d, 0);
        requires t == view.lsize();
        // requires t.exp < LOGN;
        // requires d.exp + 1 + t.exp == LOGN;
        // requires block_count(pow2_double(t)) == d.full;
        // requires block_count(t) == 2 * d.full;
    {
        var j := 0;
        a' := a;

        while (j < t.full)
            invariant view.j_loop_inv(a', d, j);
        {
            a' := j_loop(a', d, j, view);
            j := j + 1;
        }

        // j_loop_inv_post_lemma();
    }

    // method mulntt_ct()
    // {
    //     var d := pow2(LOGN);
    //     var t := pow2(0);
    //     Nth_root_lemma();

    //     while (t.full < N)
    //         invariant d.exp + t.exp == LOGN;
    //         invariant t.exp <= LOGN;
    //         invariant block_count(t) == d.full;
    //     {
    //         d := pow2_half(d);

    //         block_count_half_lemma(pow2_double(t));
    //         // assert block_count(pow2_double(t)) == d.full;
    //         // assert block_count(t) == 2 * d.full;

    //         // assert d.exp + 1 + t.exp == LOGN;
    //         // assume d.full * 2 * t.full == N;
    //         j_loop(t, d);
    //         t := pow2_double(t);
    //         // block_count_half_lemma(t);
    //     }
    // }
}