include "../../../spec/arch/msp430/machine.s.dfy"
include "../../../spec/bvop/bv16_op.s.dfy"
include "../../../spec/arch/msp430/vale.i.dfy"
include "../../../spec/crypto/falcon512.i.dfy"
include "../../generic_falcon_lemmas.dfy"

module mq_arith_lemmas refines generic_falcon_lemmas {
    import opened Seq
    import opened Power2
    import opened bv16_op_s
    import opened bv16_seq
    import opened msp_machine
    import opened msp_vale
    import opened mem

    import opened GBV = bv16_op_s

    import flat

    type uint32_view_t = dw_view_t

    lemma cond_set_Q_lemma(flags0: flags_t, mask: uint16, flags1: flags_t)
        requires (mask, flags1) == msp_subc(0, 0, flags0);
        ensures uint16_and(12289, mask) == if flags0.cf == 1 then 12289 else 0;
    {
        assert uint16_and(Q, 0xFFFF) == Q by { reveal_and(); }
        assert uint16_and(Q, 0) == 0 by { reveal_and(); }
    }

    lemma lemma_mq_add_correct(sum: uint16, mask: uint16, r: uint16, x: uint16, y: uint16)
        requires 0 <= x < 12289;
        requires 0 <= y < 12289;
        requires sum == msp_add(x, msp_add(y, 0xcfff).0).0;
        requires mask == msp_sub(0, if sum >= 0x8000 then 1 else 0).0;
        requires r == msp_add(sum, uint16_and(12289, mask)).0;
        ensures r == MQP.mqadd(x, y);
    {
        assert Q == 12289;

        // d == x + y - Q
        assert IsModEquivalent(sum, x + y - Q, BASE_16);

        // -Q <= d < Q
        assert 0 <= x + y < 2*Q;
        assert (-(Q as int)) <= x + y - Q < Q;

        if sum >= 0x8000 {
            assert mask == 0xFFFF;
            assert uint16_and(Q, 0xFFFF) == Q by { reveal_and(); }
            assert IsModEquivalent(r, x + y, Q);
        } else {
            assert mask == 0;
            assert uint16_and(Q, 0) == 0 by { reveal_and(); }
            assert IsModEquivalent(r, x + y, Q);
        }
    } 

    lemma lemma_mq_sub_correct(diff: uint16, flags: flags_t, mask: uint16, r: uint16, x: int, y: int)
        requires 0 <= x < 12289;
        requires 0 <= y < 12289;
        requires var (d, f) := msp_sub(x, y);
                 diff == d && flags == f;
        requires mask == msp_sub(0, if x - y >= 0 then 0 else 1).0;
        requires var (s, _) := msp_subc(0, 0xFFFF, flags);
                 mask == s;
        requires r == msp_add(diff, uint16_and(12289, mask)).0;
        ensures r == MQP.mqsub(x, y);
    {
        var Q : int := 12289;
        
        assert IsModEquivalent(diff, x - y, BASE_16);
        
        if get_cf(flags) == 0 {
            assert mask == 0xFFFF;
            assert uint16_and(Q, 0xFFFF) == Q by { reveal_and(); }
            assert IsModEquivalent(r, x - y, Q);
        } else {
            assert mask == 0;
            assert uint16_and(Q, 0) == 0 by { reveal_and(); }
            assert IsModEquivalent(r, x - y, Q);
        }
    }

    lemma lemma_cond_add_Q(flags: flags_t, mask: uint16, r: uint16, input: uint16)
        requires mask == msp_sub(0, if get_cf(flags) == 1 then 1 else 0).0;
        requires var (s, _) := msp_subc(0, 0, flags);
                 mask == s;
        //requires input < BASE_16 - Q;
        requires r == msp_add(input, uint16_and(12289, mask)).0;
        ensures IsModEquivalent(r, input + if get_cf(flags) == 1 then Q else 0, BASE_16);
    {
        if get_cf(flags) == 1 {
            assert mask == 0xFFFF;
            assert uint16_and(Q, 0xFFFF) == Q by { reveal_and(); }
        } else {
            assert mask == 0;
            assert uint16_and(Q, 0) == 0 by { reveal_and(); }
        }
    }

    lemma lemma_montymul_correct(x: nat, y: nat, xy_lh: uint16, xy_uh: uint16, Q0Ixy:nat, sum: uint32_view_t, partial_lh: uint16, partial_uh: uint16, partial_uh_xy_uh:uint16, m: uint16, flags: flags_t, rr:uint16)
        requires x < Q;
        requires y < Q;
        requires to_nat([xy_lh, xy_uh]) == x * y;
        requires Q0Ixy == mul(xy_lh, 12287);
        requires sum.lh == partial_lh;
        requires sum.uh == partial_uh;
        requires sum.full == Q * Q0Ixy + xy_lh;
        requires partial_uh_xy_uh == msp_add(partial_uh, xy_uh).0;
        requires m == msp_sub(partial_uh_xy_uh, Q).0;
        requires flags == msp_sub(partial_uh_xy_uh, Q).1;
        requires IsModEquivalent(rr, m + if get_cf(flags) == 1 then Q else 0, BASE_16);
        ensures IsModEquivalent(rr * 4091, x * y, Q);
    {
        var v := (12287 * x * y) % BASE_16;
        assert x * y == xy_lh + xy_uh * BASE_16 by { bv16_seq.LemmaSeqLen2([xy_lh, xy_uh]); }
        assert xy_lh == (x * y) % BASE_16 by { LemmaModMultiplesVanish(xy_uh, xy_lh, BASE_16); }
        calc {
            Q0Ixy;
                { reveal dw_lh(); }
            (xy_lh * 12287) % BASE_16;
            (((x * y) % BASE_16) * 12287) % BASE_16;
                { LemmaMulModNoopGeneral(x*y, 12287, BASE_16); }
            ((x * y) * 12287) % BASE_16;
                { LemmaMulIsCommutativeAuto(); LemmaMulIsAssociativeAuto(); }
            v;
        }
        assert v == Q0Ixy;
        var w := Q * v;
        var xy := x * y;
        var z := partial_uh_xy_uh;

        // Establish a bound on xy_uh and partial_uh,
        // so we can show that their sum doesn't overflow

        // Bound xy_uh
        assert x * y <= (Q-1) * (Q-1) by { LemmaMulUpperBound(x, Q-1, y, Q-1); }
        assert x * y == BASE_16 * ((x * y)/BASE_16) + (x * y) % BASE_16 by { LemmaFundamentalDivMod(x*y, BASE_16); }
        assert x * y == BASE_16 * ((x * y)/BASE_16) + xy_lh;
        assert xy_uh * BASE_16 == BASE_16 * ((x * y)/BASE_16);
        assert xy_uh == (x * y) / BASE_16;
        assert (x * y) / BASE_16 <= ((Q-1) * (Q-1))/BASE_16 by { LemmaDivIsOrdered(x*y, (Q-1)*(Q-1), BASE_16); }
        assert xy_uh <= 2304;

        // Bound partial_uh
        calc {
            Q * Q0Ixy + xy_lh;
            sum.full;
            { dw_view_lemma(sum); }
            partial_lh + partial_uh * BASE_16; 
        }
        assert Q0Ixy < BASE_16;
        assert Q*Q0Ixy <= Q*(BASE_16-1) by { LemmaMulUpperBound(Q, Q, Q0Ixy, BASE_16-1); }
        assert Q*Q0Ixy + xy_lh <= Q*(BASE_16-1) + BASE_16; 
        assert (Q*Q0Ixy + xy_lh)/BASE_16 <= (Q*(BASE_16-1) + BASE_16) / BASE_16 by { LemmaDivIsOrdered(Q*Q0Ixy + xy_lh, Q*(BASE_16-1) + BASE_16, BASE_16); }
        assert (partial_lh + partial_uh * BASE_16)/BASE_16 <= (Q*(BASE_16-1) + BASE_16) / BASE_16;
        assert (partial_lh + partial_uh * BASE_16)/BASE_16 <= 12290;
        assert partial_uh <= 12290 by { LemmaDivMultiplesVanishFancy(partial_uh, partial_lh, BASE_16); }

        // Bringing the two bounds together:
        assert partial_uh + xy_uh < BASE_16;
        assert partial_uh_xy_uh == partial_uh + xy_uh;

        // Connect a 32-bit spec to our 16-bit calculations
        calc {
            Q * Q0Ixy + xy;
            Q * Q0Ixy + xy_lh + xy_uh * BASE_16;
            sum.full + xy_uh * BASE_16;
            calc {
                sum.full;
                    { dw_view_lemma(sum); }
                partial_lh + partial_uh * BASE_16; 
            }
            partial_lh + partial_uh * BASE_16 + xy_uh * BASE_16;
            { LemmaMulIsDistributiveAuto(); }
            partial_lh + (partial_uh + xy_uh) * BASE_16; 
            partial_uh_xy_uh * BASE_16 + partial_lh;
        }
        assert partial_uh_xy_uh * BASE_16 + partial_lh == Q * Q0Ixy + xy;

        gbassert IsModEquivalent(w + xy, 0, BASE_16) by {
            assert IsModEquivalent(v, 12287 * x * y, BASE_16);
            assert Q == 12289;
            assert BASE_16 == 65536;
            assert w == Q * v;
            assert xy == x * y;
        }

        DivMod.LemmaFundamentalDivMod(w + xy, BASE_16);
        assert w + xy == BASE_16 * (w+xy) / BASE_16 + (w+xy) % BASE_16;
        assert w + xy == BASE_16 * (w+xy) / BASE_16; 
        Power2.Lemma2To64();
        assert z * BASE_16 == w + xy;

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

    predicate elems_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(heap, iter) 
        && (address >= 0 ==> iter.cur_ptr() == address)
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && valid_elems(iter.buff)
    }

    predicate is_nelem(e: uint16)
    {
        MQN.int_is_normalized(bv16_op_s.to_int16(e))
    }

    function as_nelem(e: uint16): nelem
        requires is_nelem(e)
    {
        bv16_op_s.to_int16(e)
    }

    predicate {:opaque} valid_nelems(a: seq<uint16>)
        ensures valid_nelems(a) ==> |a| == N.full;
    {
        && |a| == N.full
        && (forall i | 0 <= i < |a| :: is_nelem(a[i]))
    }

    function as_nelems(a: seq<uint16>): (na: seq<nelem>)
        requires valid_nelems(a);
    {
        reveal valid_nelems();
        seq(|a|, i requires 0 <= i < |a| => as_nelem(a[i]))
    }

    predicate nelems_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(heap, iter)
        && (address >= 0 ==> iter.cur_ptr() == address)
        && (index >= 0 ==> iter.index == index)
        && valid_nelems(iter.buff)
    }

    predicate denorm_inv(nv: seq<uint16>, dnv: seq<uint16>, i: nat)
    {
        && valid_nelems(nv)
        && valid_elems(dnv)
        && reveal valid_nelems();
        && i <= N.full
        && (forall j | 0 <= j < i :: 
            dnv[j] == MQN.denormalize(as_nelem(nv[j])))
    }

    lemma denorm_inv_peri_lemma(nv: seq<uint16>, dnv: seq<uint16>, i: nat, a: uint16, b: uint16)
        requires i < N.full;
        requires denorm_inv(nv, dnv, i);
        requires a == nv[i];
        requires var adj := if to_int16(a) < 0 then Q else 0;
            b == msp_add(adj, a).0;
        ensures denorm_inv(nv, dnv[i := b], i+1);
    {
        reveal valid_elems();
        reveal valid_nelems();
        assert is_nelem(nv[i]);
        assert b == MQN.denormalize(as_nelem(a));
    }

    // 0 <= e < Q -> -Q/2 <= e <= Q/2
    predicate {:opaque} norm_inv(outputs: seq<uint16>, inputs: seq<uint16>, i: nat)
    {
        && valid_elems(inputs)
        && |outputs| == N.full
        && reveal valid_elems();
        && i <= N.full
        && inputs[i..] == outputs[i..]
        && (forall j | 0 <= j < i :: (
            && is_nelem(outputs[j])
            && as_nelem(outputs[j]) == MQN.normalize(inputs[j]))
        )
    }

    lemma norm_pre_lemma(inputs: seq<uint16>)
        requires valid_elems(inputs);
        ensures norm_inv(inputs, inputs, 0);
    {
        reveal norm_inv();
    }

    lemma norm_peri_lemma(outputs: seq<uint16>, inputs: seq<uint16>, i: nat,
        w: uint16, fg: flags_t, diff: uint16, mask: uint16, rst: uint16)
        requires norm_inv(outputs, inputs, i);
        requires i < |outputs|;
        requires w == outputs[i];
        requires (diff, fg) == msp_sub(6144, w);
        requires fg.cf == 1 ==> mask == 12289;
        requires fg.cf == 0 ==> mask == 0;
        requires rst == uint16_sub(w, mask);
        ensures norm_inv(outputs[i := rst], inputs, i + 1);
    {
        reveal norm_inv();
        reveal valid_elems();

        if 6144 - w < 0 {
            assert mask == 12289;
        } else {
            assert mask == 0;
        }
    }

    lemma norm_post_lemma(outputs: seq<uint16>, inputs: seq<uint16>)
        requires valid_elems(inputs);
        requires norm_inv(outputs, inputs, 512);
        ensures valid_nelems(outputs);
    {
        reveal norm_inv();
        reveal valid_nelems();
    }

    lemma forward_s_loop_inv_pre_lemma(
        a: seq<nat>,
        d: pow2_t,
        j: uint16,
        t: pow2_t,
        u: uint16,
        w: uint16,
        s: uint16,
        s_end: uint16,
        view: FNTT.loop_view)

        requires forward_j_loop_inv(a, d, j, u, view);
        requires t == view.lsize();
        requires j < view.lsize().full;
        requires var w0 := uint16_add(t.full, j);
            w == uint16_add(w0, w0);
        requires s == uint16_add(u, u);
        requires d.full * 2 < BASE_16;
        requires s_end == uint16_add(d.full * 2, s);
        ensures s == 2 * u;
        ensures s_end == (d.full + u) * 2;
        ensures w == (t.full + j) * 2;
        ensures forward_s_loop_inv(a, d, j, 0, view);
        ensures t.full + j < N.full;
        ensures |FNTT.rev_mixed_powers_mont_table()| == N.full;
        ensures FNTT.rev_mixed_powers_mont_table()[t.full + j] == 
            MQP.mqmul(FNTT.rev_mixed_powers_mont_x_value(2 * j, d), R);
    {
        view.s_loop_inv_pre_lemma(as_elems(a), d, j);
        FNTT.rev_mixed_powers_mont_table_lemma(t, d, j);

        assert u == j * (2 * d.full);
        assert d == view.hcount();

        var p := pow2_mul(t, d);
        assert p.exp == 8;
        assume p.full == 256;

        calc {
            u;
            j * (2 * d.full);
            <= 
            {
                LemmaMulInequality(j, t.full, 2 * d.full);
            }
            t.full * (2 * d.full);
            {
                LemmaMulProperties();
            }
            2 * (t.full * d.full);
            2 * p.full;
            512;
        }
    }

    lemma forward_s_loop_inv_post_lemma(
        a: seq<nat>,
        d: pow2_t,
        j: nat,
        u: uint16,
        bi: nat,
        view: FNTT.loop_view)
    
        requires bi == d.full;
        requires 2 * d.full < BASE_16;
        requires u == j * (2 * d.full);
        requires forward_s_loop_inv(a, d, j, bi, view);

        ensures uint16_add(2 * d.full, u) == (j + 1) * (2 * d.full);
        ensures forward_j_loop_inv(a, d, j + 1, u + 2 * d.full, view);
    {
        view.s_loop_inv_post_lemma(as_elems(a), d, j, bi);

        var t := view.lsize();
        var p := pow2_mul(t, d);
        assert p.exp == 8;
        assume p.full == 256;

        assert u + 2 * d.full == (j + 1) * (2 * d.full) by{
            LemmaMulProperties();
        }

        calc {
            (j + 1) * (2 * d.full);
            <= 
            {
                LemmaMulInequality(j+1, t.full, 2 * d.full);
            }
            t.full * (2 * d.full);
            {
                LemmaMulProperties();
            }
            2 * (t.full * d.full);
            2 * p.full;
            512;
        }
    }

    lemma forward_s_loop_index_lemma(
        a: seq<nat>,
        d: pow2_t,
        j: nat,
        s: uint16,
        bi: nat,
        view: FNTT.loop_view)
        returns (gs: nat)

        requires forward_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        requires 2 * d.full < BASE_16;
        requires s == (bi + j * (2 * d.full)) * 2;

        ensures s == 2 * gs;
        ensures s + 2 * d.full == 2 * (gs + d.full);
        ensures gs + d.full < N.full;
        ensures a[gs] == CPV.level_points_view(a, view.hsize)[bi][2*j];
        ensures gs == CPV.point_view_index(bi, 2*j, view.hsize);
        ensures a[gs+d.full] == CPV.level_points_view(a, view.hsize)[bi][2*j+1];
        ensures gs+d.full == CPV.point_view_index(bi, 2*j+1, view.hsize);
        ensures a[gs+d.full] < Q;
        ensures a[gs] < Q;
    {
        gs := view.higher_points_view_index_lemma(as_elems(a), d, j, bi);
        assert s == 2 * gs by {
            LemmaMulProperties();
        }
        reveal valid_elems();
    }

    lemma inverse_s_loop_inv_pre_lemma(
        a: seq<nat>,
        d: pow2_t,
        j: uint16,
        t: pow2_t,
        u: uint16,
        w: uint16,
        s: uint16,
        s_end: uint16,
        view: INTT.loop_view)

        requires inverse_j_loop_inv(a, d, j, u, view);
        requires t == view.lsize();
        requires j < view.lsize().full;
        requires var w0 := uint16_add(t.full, j);
            w == uint16_add(w0, w0);
        requires s == uint16_add(u, u);
        requires d.full * 2 < BASE_16;
        requires s_end == uint16_add(d.full * 2, s);
        ensures s == 2 * u;
        ensures s_end == (d.full + u) * 2;
        ensures w == (t.full + j) * 2;
        ensures inverse_s_loop_inv(a, d, j, 0, view);
        ensures t.full + j < N.full;
        ensures |INTT.rev_omega_inv_powers_mont_table()| == N.full;
        ensures INTT.rev_omega_inv_powers_mont_table()[t.full + j] == 
            MQP.mqmul(INTT.rev_omega_inv_powers_x_value(2 * j, d), R);
    {
        view.s_loop_inv_pre_lemma(as_elems(a), d, j);
        INTT.rev_omega_inv_powers_mont_table_lemma(t, d, j);

        assert u == j * (2 * d.full);
        assert d == view.hcount();

        var p := pow2_mul(t, d);
        assert p.exp == 8;
        assume p.full == 256;

        calc {
            u;
            j * (2 * d.full);
            <= 
            {
                LemmaMulInequality(j, t.full, 2 * d.full);
            }
            t.full * (2 * d.full);
            {
                LemmaMulProperties();
            }
            2 * (t.full * d.full);
            2 * p.full;
            512;
        }
    }

    lemma inverse_s_loop_inv_post_lemma(
        a: seq<nat>,
        d: pow2_t,
        j: nat,
        u: uint16,
        bi: nat,
        view: INTT.loop_view)
    
        requires bi == d.full;
        requires 2 * d.full < BASE_16;
        requires u == j * (2 * d.full);
        requires inverse_s_loop_inv(a, d, j, bi, view);

        ensures uint16_add(2 * d.full, u) == (j + 1) * (2 * d.full);
        ensures inverse_j_loop_inv(a, d, j + 1, u + 2 * d.full, view);
    {
        view.s_loop_inv_post_lemma(as_elems(a), d, j, bi);

        var t := view.lsize();
        var p := pow2_mul(t, d);
        assert p.exp == 8;
        assume p.full == 256;

        assert u + 2 * d.full == (j + 1) * (2 * d.full) by{
            LemmaMulProperties();
        }

        calc {
            (j + 1) * (2 * d.full);
            <= 
            {
                LemmaMulInequality(j+1, t.full, 2 * d.full);
            }
            t.full * (2 * d.full);
            {
                LemmaMulProperties();
            }
            2 * (t.full * d.full);
            2 * p.full;
            512;
        }
    }

    lemma inverse_s_loop_index_lemma(
        a: seq<nat>,
        d: pow2_t,
        j: nat,
        s: uint16,
        bi: nat,
        view: INTT.loop_view)
        returns (gs: nat)

        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        requires 2 * d.full < BASE_16;
        requires s == (bi + j * (2 * d.full)) * 2;

        ensures s == 2 * gs;
        ensures s + 2 * d.full == 2 * (gs + d.full);
        ensures gs + d.full < N.full;
        ensures a[gs] == CPV.level_points_view(a, view.hsize)[bi][2*j];
        ensures gs == CPV.point_view_index(bi, 2*j, view.hsize);
        ensures a[gs+d.full] == CPV.level_points_view(a, view.hsize)[bi][2*j+1];
        ensures gs+d.full == CPV.point_view_index(bi, 2*j+1, view.hsize);
        ensures a[gs+d.full] < Q;
        ensures a[gs] < Q;
    {
        gs := view.higher_points_view_index_lemma(as_elems(a), d, j, bi);
        assert s == 2 * gs by {
            LemmaMulProperties();
        }
        reveal valid_elems();
    }

    lemma bit_rev_index_lemma(
        a: seq<nat>,
        ftable: seq<nat>,
        li: nat,
        ri: nat,
        ti: nat)

        requires |a| == N.full;
        requires bit_rev_ftable_wf(ftable);

        requires 0 <= 2 * ti + 1 < |ftable|;
        requires li == ftable[2 * ti];
        requires ri == ftable[2 * ti+1];

        ensures li == build_view(a, ti, N).get_split_index();
        ensures ri == bit_rev_int(ftable[2 * ti], N);
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
        assert li == build_view(a, ti, N).get_split_index();
        assert ri == bit_rev_int(ftable[2 * ti], N);
    }

    const NORMSQ_BOUND := 0x100000000

    function l2norm_squared(s1: seq<uint16>, s2: seq<uint16>, i: nat): nat
        requires |s1| == |s2|
        requires i <= |s1|
    {
        if i == 0 then
            0
        else
            var v1, v2 := s1[i-1] as int, s2[i-1] as int;
            LemmaMulStrictlyPositive(v1, v1);
            LemmaMulStrictlyPositive(v2, v2);
            var vv1, vv2 := v1 * v1, v2 * v2;
            l2norm_squared(s1, s2, i-1) + vv1 + vv2
    }
}
