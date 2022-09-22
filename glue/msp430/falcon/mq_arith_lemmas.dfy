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

    lemma montmul_lemma(x: uint16, y: uint16, cf: uint1, 
        xy_lh: uint16, xy_uh: uint16, sum: uint32_view_t, rr: uint16)
        requires x < Q;
        requires y < Q;
        requires to_nat([xy_lh, xy_uh]) == x * y;
        requires sum.full + cf * 0x100000000 == 
            x * y + mul(xy_lh, 12287) * 12289;
        requires rr == if sum.uh >= Q then sum.uh - Q else sum.uh;
        ensures rr == montmul(x, y);
    {
        var s_lh: nat, s_uh: nat := sum.lh, sum.uh;
        var s_full: nat := sum.full;
        var t := (xy_lh * 12287) % 65536;

        assert x * y + t * 12289 <= 956379136 by {
            LemmaMulUpperBound(x, Q, y, Q);
        }
        assert s_full == x * y + t * 12289 by {
            reveal dw_lh();
        }
        assert s_lh + s_uh * 65536 == s_full by {
            dw_view_lemma(sum);
        }
        assert x * y == xy_lh + xy_uh * 65536 by {
            bv16_seq.LemmaSeqLen2([xy_lh, xy_uh]);
        }

        gbassert IsModEquivalent(s_lh, 0, 65536) by {
            assert s_lh + s_uh * 65536 == x * y + t * 12289;
            assert x * y == xy_lh + xy_uh * 65536;
            assert IsModEquivalent(t, xy_lh * 12287, 65536);
        }

        LemmaSmallMod(s_lh, 65536);
        assert s_lh == 0;
        MQ.Nth_root_lemma();
        var R_INV := R_INV;
        var sub := if s_uh >= Q then 1 else 0;

        gbassert IsModEquivalent(rr, x * y * R_INV, 12289) by {
            assert rr == s_uh - sub * 12289;
            assert sub * (sub - 1) == 0;
            assert BASE_16 == 65536;
            assert s_uh * 65536 == x * y + t * 12289;
            assert x * y == xy_lh + xy_uh * 65536;
            assert IsModEquivalent(t, xy_lh * 12287, 65536);
            assert IsModEquivalent(1, R_INV * BASE_16, 12289);
        }

        assert s_uh * 65536 == s_full;
        assert s_uh <= 14593;
        LemmaSmallMod(rr, 12289);
    }

    predicate elems_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(heap, iter) 
        && (address >= 0 ==> iter.cur_ptr() == address)
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && valid_elems(iter.buff)
    }

    predicate valid_nelem(e: uint16)
    {
        MQN.int_is_normalized(bv16_op_s.to_int16(e))
    }

    function as_nelem(e: uint16): nelem
        requires valid_nelem(e)
    {
        bv16_op_s.to_int16(e)
    }

    predicate {:opaque} valid_nelems(a: seq<uint16>)
        ensures valid_nelems(a) ==> |a| == N.full;
    {
        && |a| == N.full
        && (forall i | 0 <= i < |a| :: valid_nelem(a[i]))
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
        assert valid_nelem(nv[i]);
        assert b == MQN.denormalize(as_nelem(a));
    }

    // 0 <= e < Q -> -Q/2 <= e <= Q/2
    predicate {:opaque} norm_inv(outputs: seq<uint16>, inputs: seq<uint16>, i: nat)
        ensures norm_inv(outputs, inputs, i) ==> |outputs| == N.full
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
        requires i <= N.full;
        requires valid_nelems(s1);
        requires valid_nelems(s2);
    {
        var ns1 := as_nelems(s1);
        var ns2 := as_nelems(s2);
        MQN.l2norm_squared(ns1, ns2, i)
    }

    lemma accumulate_lemma(v16: uint16,
        sum: uint32_view_t, sum': uint32_view_t,
        cf: uint1, mask: uint16,
        over: uint16, over': uint16, gsum: nat)
        returns (gsum': nat)

        requires over == 0xFFFF || over == 0;
        requires over == 0 ==> sum.full == gsum;
        requires over == 0xFFFF ==> gsum >= 0x100000000;

        requires valid_nelem(v16);
        requires sum'.full + 0x100000000 * cf 
            == sum.full + v16 * v16;

        requires mask == if cf == 1 then 0xFFFF else 0;
        requires over' == uint16_or(mask, over);

        ensures over' == 0xFFFF || over' == 0;
        ensures over' == 0 ==> sum'.full == gsum';
        ensures over' == 0xFFFF ==> gsum' >= 0x100000000;
        ensures gsum' == gsum + as_nelem(v16) * as_nelem(v16);
    {
        or_consts_lemma();
        var iv16 :int := bv16_op_s.to_int16(v16);
        assume 0 <= iv16 * iv16 <= 151019521;
        assume (iv16 * iv16) == v16 * v16;
        gsum' := gsum + v16 * v16;
    }

    lemma falcon_lemma(
        tt0: seq<uint16>, tt1: seq<uint16>, tt2: seq<uint16>,
        s1: seq<uint16>, s2: seq<uint16>, h: seq<uint16>, c0: seq<uint16>,
        result: uint16)

    requires valid_elems(tt0);
    requires valid_elems(tt1);
    requires valid_elems(h);
    requires denorm_inv(s2, tt0, 512);
    requires as_elems(tt1) ==
            poly_mod_product(as_elems(tt0), as_elems(h));
    requires poly_sub_loop_inv(tt2, tt1, c0, 512);
    requires norm_inv(s1, tt2, 512);
    requires valid_nelems(s1);
    requires valid_nelems(s2);
    requires (result == 1)
            <==> 
        l2norm_squared(s1, s2, 512) < 0x29845d6;
    ensures (result == 1)
            <==>
        falcon_verify(as_elems(c0), as_nelems(s2), as_elems(h));
    {
        reveal valid_nelems();
        reveal valid_elems();
        reveal norm_inv();

        assert tt0 == MQN.denormalize_elems(as_nelems(s2));
        assert tt1 == poly_mod_product(as_elems(tt0), as_elems(h));
        assert tt2 == MQP.poly_sub(tt1, c0);
        assert as_nelems(s1) == MQN.normalize_elems(tt2);
        assert l2norm_squared(s1, s2, 512) == 
            MQN.l2norm_squared(as_nelems(s1), as_nelems(s2), 512);
    }

    lemma or_consts_lemma()
        ensures uint16_or(0xFFFF, 0xFFFF) == 0xFFFF;
        ensures uint16_or(0xFFFF, 0) == 0xFFFF;
        ensures uint16_or(0, 0xFFFF) == 0xFFFF;
        ensures uint16_or(0, 0) == 0;
    {
        reveal_or();
    }
}
