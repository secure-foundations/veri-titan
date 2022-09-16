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
    import opened GBV = bv32_op_s

    predicate elems_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(iter, heap, if address >= 0 then address else iter.cur_ptr())
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && valid_elems(iter.buff)
    }

    predicate nelems_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(iter, heap, if address >= 0 then address else iter.cur_ptr())
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && valid_nelems(iter.buff)
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

    predicate valid_nelem(e: uint16)
    {
        MQN.int_is_normalized(bv16_op_s.to_int16(e))
    }

    predicate valid_nelems(a: seq<uint16>)
    {
        && |a| == N.full
        && (forall i | 0 <= i < |a| :: valid_nelem(a[i]))
    }

    function as_nelems(a: seq<uint16>): (na: seq<nelem>)
        requires valid_nelems(a);
    {
        seq(|a|, i requires 0 <= i < |a| => as_nelem(a[i]))
    }

    function as_nelem(e: uint16): nelem
        requires valid_nelem(e)
    {
        bv16_op_s.to_int16(e)
    }

    lemma denormalize_lemma(buff: seq<uint16>, i: nat, a1: uint32, b: uint32, c: uint32, d: uint32)
        requires valid_nelems(buff);
        requires i < |buff|;
        requires a1 == uint16_sign_ext(buff[i]);
        requires b == uint32_srai(a1, 31);
        requires c == uint32_and(b, Q);
        requires d == uint32_add(a1, c);
        ensures valid_nelem(buff[i]);
        ensures d == MQN.denormalize(as_nelem(buff[i]));
    {
        assert valid_nelem(buff[i]);

        var a0 :uint16 := buff[i];
        var sa0 := as_nelem(a0);
        assert sa0 < 0 ==> a1 == a0 as nat + 0xffff0000;
        assert sa0 >= 0 ==> a1 == a0;

        if to_int32(a1) >= 0 {
            assert sa0 >= 0;
            assert b == 0 by { lemma_rs_by_31(to_int32(a1)); }
            lemma_uint32_and_Q(b);
            assert c == 0;
            assert d == a0;
            assert d == MQN.denormalize(as_nelem(a0));
        }
        else {
            assert sa0 < 0;
            assert int32_rs(to_int32(a1), 31) == -1 by { lemma_rs_by_31(to_int32(a1)); }
            lemma_uint32_and_Q(b);
            assert c == Q;
            assert d == sa0 + Q;
            assert d == MQN.denormalize(as_nelem(a0));
        }
    }

    predicate denormalization_inv(nv: seq<uint16>, dnv: seq<uint16>, i: nat)
    {
        && valid_nelems(nv)
        && valid_elems(dnv)
        && i <= N.full
        && (forall j | 0 <= j < i :: 
            dnv[j] == MQN.denormalize(as_nelem(nv[j])))
    }

    lemma denormalization_peri_lemma(buff: seq<uint16>, dnv: seq<uint16>, i: nat, a1: uint32, b: uint32, c: uint32, d: uint32)
        requires valid_nelems(buff);
        requires valid_elems(dnv);
        requires denormalization_inv(buff, dnv, i);
        requires i < |buff|;
        requires a1 == uint16_sign_ext(buff[i]);
        requires b == uint32_srai(a1, 31);
        requires c == uint32_and(b, Q);
        requires d == uint32_add(a1, c);
        ensures valid_nelem(buff[i]);
        ensures d == MQN.denormalize(as_nelem(buff[i]));
        ensures valid_elems(dnv[i := lh(d)]);
        ensures denormalization_inv(buff, dnv[i := lh(d)], i + 1);
    {
        reveal valid_elems();
        var lh, uh := lh(d), uh(d);
        half_split_lemma(d);
        denormalize_lemma(buff, i, a1, b, c, d);
        assert d == lh;
    }
    
    // 0 <= e < Q -> -Q/2 <= e <= Q/2
    predicate {:opaque} normalization_inv(outputs: seq<uint16>,  inputs: seq<uint16>, i: nat)
    {
        && valid_elems(inputs)
        && |outputs| == N.full
        && reveal valid_elems();
        && i <= N.full
        && inputs[i..] == outputs[i..]
        && (forall j | 0 <= j < i :: (
            && valid_nelem(outputs[j])
            && as_nelem(outputs[j]) == MQN.normalize(inputs[j]))
        )
    }

    lemma normalization_pre_lemma(inputs: seq<uint16>)
        requires valid_elems(inputs);
        ensures normalization_inv(inputs, inputs, 0);
    {
        reveal normalization_inv();
    }

    function cond_Q(src: uint32): uint32
    {
        if to_int32(src) >= 0 then 0 else 12289
    }

    lemma normalization_peri_lemma(outputs: seq<uint16>, inputs: seq<uint16>, i: nat, value: uint32, diff: uint32, mask: uint32, rst: uint32)
        requires normalization_inv(outputs, inputs, i);
        requires i < |outputs|;
        requires value == uint16_sign_ext(outputs[i])
        requires diff == uint32_sub(Q/2, value);
        requires mask == cond_Q(diff);
        requires rst == uint32_sub(value, mask);
        ensures normalization_inv(outputs[i := lh(rst)], inputs, i + 1);
    {
        reveal valid_elems();
        reveal normalization_inv();

        assert value == outputs[i];
        half_split_lemma(rst);
        var lh, uh := lh(rst), uh(rst);

        if to_int32(diff) >= 0 {
            assert as_nelem(rst) == MQN.normalize(value);
        } else {
            if to_int32(rst) < 0 {
                assume uh == 0xffff; // the upper bits all set
            } else {
                assume uh == 0; // the upper bits all clear
            }
        }
        assert as_nelem(lh) == MQN.normalize(value);
    }

    lemma normalization_post_lemma(outputs: seq<uint16>, inputs: seq<uint16>)
        requires valid_elems(inputs);
        requires normalization_inv(outputs, inputs, 512);
        ensures valid_nelems(outputs);
    {
        reveal normalization_inv();
    }

    const NORMSQ_BOUND := integers.BASE_31

    function l2norm_squared(s1: seq<uint16>, s2: seq<uint16>, i: nat): nat
        requires i <= N.full;
        requires valid_nelems(s1);
        requires valid_nelems(s2);
    {
        var ns1 := as_nelems(s1);
        var ns2 := as_nelems(s2);
        MQN.l2norm_squared(ns1, ns2, i)
    }

    lemma accumulate_lemma(v16: uint16, sum: uint32, sum': uint32,
        over: uint32, over': uint32, gsum: nat)
        returns (gsum': nat)
        requires msb(over) == 1 ==> gsum >= NORMSQ_BOUND;
        requires msb(over) == 0 ==> sum == gsum < NORMSQ_BOUND;

        requires valid_nelem(v16);
        requires var v32 := uint16_sign_ext(v16);
            sum' == uint32_add(sum, uint32_mul(v32, v32));
        requires over' == uint32_or(over, sum');

        ensures gsum' == gsum + as_nelem(v16) * as_nelem(v16);
        ensures msb(over') == 1 ==> gsum' >= NORMSQ_BOUND;
        ensures msb(over') == 0 ==> sum' == gsum' < NORMSQ_BOUND;
    {
        var v32 := uint16_sign_ext(v16);
        var iv16 :int := bv16_op_s.to_int16(v16);
        var iv32 :int := to_int32(v32);
        var p := uint32_mul(v32, v32);
        gsum' := gsum + p;

        mul_equiv_lemma(iv32, iv32);

        assert -12289 <= iv16 <= 12289;
        assume 0 <= iv16 * iv16 <= 151019521;

        calc == {
            p;
            (iv32 * iv32) % 0x100000000;
            (iv16 * iv16) % 0x100000000;
            {
                LemmaSmallMod(151019521, 0x100000000);
            }
            (iv16 * iv16);
        }

        assert msb(sum') == 1 ==> msb(over') == 1 by {
            reveal or();
        }
        assert msb(over) == 1 ==> msb(over') == 1 by {
            reveal or();
        }
        assume (msb(sum') == 0 && msb(over) == 0)
            ==> msb(over') == 0;
    }

    lemma is_short_post_lemma(s1: seq<uint16>, s2: seq<uint16>, 
        sum: uint32, sum': uint32, over: uint32, over': uint32, gsum: nat)
        requires valid_nelems(s1);
        requires valid_nelems(s2);
        requires gsum == l2norm_squared(s1, s2, N.full);
        requires msb(over) == 1 ==> gsum >= NORMSQ_BOUND;
        requires msb(over) == 0 ==> sum == gsum < NORMSQ_BOUND;
        requires over' == uint32_srai(over, 31);
        requires sum' == or(over', sum);
        ensures gsum < NORMSQ_BOUND ==> sum' == sum;
        ensures gsum >= NORMSQ_BOUND ==> sum' == 0xffff_ffff;
    {
        lemma_rs_by_31(to_int32(over));

        if (msb(over) == 0) {
            assert over' == 0;
            assert sum' == sum by {
                reveal or();
            }
        } else {
            assert over' == 0xffff_ffff;
            assert sum' == 0xffff_ffff by {
                reveal or();
            }
        }
    }

    lemma falcon_lemma(
        tt0: seq<uint16>, tt1: seq<uint16>, tt2: seq<uint16>,
        s1: seq<uint16>, s2: seq<uint16>, h: seq<uint16>, c0: seq<uint16>,
        result: uint32)

    requires valid_elems(tt0);
    requires valid_elems(tt1);
    requires valid_elems(h);
    requires denormalization_inv(s2, tt0, 512);
    requires as_elems(tt1) ==
            poly_mod_product(as_elems(tt0), as_elems(h));
    requires poly_sub_loop_inv(tt2, tt1, c0, 512);
    requires normalization_inv(s1, tt2, 512);
    requires valid_nelems(s1);
    requires valid_nelems(s2);
    requires (result == 1) <==>
        l2norm_squared(s1, s2, 512) < 0x29845d6;
    ensures (result == 1) <==>
        falcon_verify(as_elems(c0), as_nelems(s2), as_elems(h));
    {
        reveal valid_elems();
        reveal normalization_inv();

        assert tt0 == MQN.denormalize_elems(as_nelems(s2));
        assert tt1 == poly_mod_product(as_elems(tt0), as_elems(h));
        assert tt2 == MQP.poly_sub(tt1, c0);
        assert as_nelems(s1) == MQN.normalize_elems(tt2);
        assert l2norm_squared(s1, s2, 512) == 
            MQN.l2norm_squared(as_nelems(s1), as_nelems(s2), 512);
    }

}
