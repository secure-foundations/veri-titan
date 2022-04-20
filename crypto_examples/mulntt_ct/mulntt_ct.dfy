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

    method j_loop(a: n_sized, d: pow2_t, j: nat, ghost view: loop_view)
    returns (a': n_sized)

        requires view.j_loop_inv(a, d, j);
        requires j < view.lsize().full;
        ensures view.j_loop_inv(a', d, j + 1);
    {
        view.s_loop_inv_pre_lemma(a, d, j);

        var u := (2 * j) * d.full;
        var w := modmul(x_value(2 * j, d), R); // TODO: read from table
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

            var x := montmul(o, w);
            a' := a[s+d.full := modsub(e, x)];
            a' := a'[s := modadd(e, x)];
            s := s + 1;

            view.s_loop_inv_peri_lemma(a, a', d, j, bi);
        }

        assert s == u + d.full;
        view.s_loop_inv_post_lemma(a', d, j, d.full);
    }

    method t_loop(a: n_sized, t: pow2_t, d: pow2_t, ghost view: loop_view)
        returns (a': n_sized, ghost view': loop_view)

        requires view.t_loop_inv(a, d);
        requires t == view.lsize();
        requires t.exp < LOGN;

        ensures view.hsize.exp < LOGN ==> view'.t_loop_inv(a', pow2_half(d));
        ensures view.hsize.exp == LOGN ==> view' == view;
        ensures view.hsize.exp == LOGN ==> view'.t_loop_end(a');
    {
        var j := 0;
        a' := a;

        view.j_loop_inv_pre_lemma(a', d);

        while (j < t.full)
            invariant view.j_loop_inv(a', d, j);
        {
            a' := j_loop(a', d, j, view);
            j := j + 1;
        }

        view' := view.j_loop_inv_post_lemma(a', d, j);
    }

    method mulntt_ct(a: n_sized, ghost view: loop_view)
        returns (a': n_sized, ghost view': loop_view)
        requires view.t_loop_inv(a, pow2(LOGN-1));
        ensures view'.t_loop_end(a');
    {
        var d := pow2(LOGN);
        var t := pow2(0);
        a' := a;
        view' := view;

        assert view'.lsize() == pow2(0) by {
            view'.size_count_lemma();
        }

        pow2_basics(t);

        Nth_root_lemma();

        while (t.full < N)
            invariant 1 <= d.exp <= LOGN;
            invariant view'.t_loop_inv(a', pow2_half(d));
            invariant t.full >= N ==> view'.hsize.exp == LOGN;
            invariant t == view'.lsize();
        {
            d := pow2_half(d);
            a', view' := t_loop(a', t, d, view');
            t := pow2_double(t);

            if t.full >= N {
                assume view'.hsize.exp == LOGN;
            }
        }

        assert view'.hsize.exp == LOGN;
    }
}