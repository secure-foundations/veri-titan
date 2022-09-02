include "bv32_falcon_lemmas.i.dfy"
include "mq_arith_lemmas.dfy"

module normalization_lemmas {
    import opened bv32_falcon_lemmas
    import opened mem
    import opened rv_machine
    import opened integers
    import opened falcon_512_i
    import opened bv32_op_s
    import opened mq_arith_lemmas

    import bv16_op_s

    const Q_HLAF :int := Q/2
    const Q := falcon_512_i.Q;
    const N := falcon_512_i.N;

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

    function uint16_buff_as_n_nelems(a: seq<uint16>): (na: seq<nelem>)
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
        requires buff_is_n_elems(dnv);
    {
        && reveal normalized_values();
        && i <= N.full
        && (forall j | 0 <= j < i :: 
            dnv[j] == MQN.denormalize(uint16_as_nelem(nv[j])))
    }

    lemma denormalization_pre_lemma(nv: seq<uint16>, dnv: seq<uint16>)
        requires normalized_values(nv);
        requires buff_is_n_elems(dnv);
        ensures denormalization_inv(nv, dnv, 0);
    {
        reveal denormalization_inv();
    }

    lemma denormalization_peri_lemma(buff: seq<uint16>, dnv: seq<uint16>, i: nat, a1: uint32, b: uint32, c: uint32, d: uint32)
        requires normalized_values(buff);
        requires buff_is_n_elems(dnv);
        requires denormalization_inv(buff, dnv, i);
        requires i < |buff|;
        requires a1 == uint16_sign_ext(buff[i]);
        requires b == uint32_srai(a1, 31);
        requires c == uint32_and(b, Q);
        requires d == uint32_add(a1, c);
        ensures uint16_is_normalized(buff[i]);
        ensures d == MQN.denormalize(uint16_as_nelem(buff[i]));
        ensures buff_is_n_elems(dnv[i := lh(d)]);
        ensures denormalization_inv(buff, dnv[i := lh(d)], i + 1);
    {
        reveal denormalization_inv();
        reveal normalized_values();
        reveal buff_is_n_elems();

        var lh, uh := lh(d), uh(d);
        half_split_lemma(d);
        assume uh == 0;
        denormalize_lemma(buff, i, a1, b, c, d);
        assert d == lh;
    }
    
    // 0 <= e < Q -> -Q/2 <= e <= Q/2
    predicate {:opaque} normalization_inv(outputs: seq<uint16>,  inputs: seq<uint16>, i: nat)
    {
        && buff_is_n_elems(inputs)
        && |outputs| == N.full
        && reveal buff_is_n_elems();
        && i <= N.full
        && inputs[i..] == outputs[i..]
        && (forall j | 0 <= j < i :: (
            && uint16_is_normalized(outputs[j])
            && uint16_as_nelem(outputs[j]) == MQN.normalize(inputs[j]))
        )
    }

    lemma normalization_pre_lemma(inputs: seq<uint16>)
        requires buff_is_n_elems(inputs);
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
    {
        reveal buff_is_n_elems();
        reveal normalization_inv();

        assert outputs[i] == inputs [i];

        cond_set_Q_lemma(b, d);

        var lh, uh := lh(e), uh(e);
        half_split_lemma(e);

        if to_int32(b) >= 0 {
            assert d == 0;
            assume uh == 0; // the upper bits all clear
            assert uint16_as_nelem(e) == MQN.normalize(a);
        } else {
            assert d == Q;
            assert 0 <= a < Q;
            assert to_int32(b) == Q_HLAF - a;
            assert Q_HLAF < a;
            assert to_int32(e) == a as int - Q;
            assert -Q_HLAF <= to_int32(e) <= Q_HLAF;
            if to_int32(e) < 0 {
                assume uh == 0xffff; // the upper bits all set
            } else {
                assume uh == 0; // the upper bits all clear
            }
            assert bv16_op_s.to_int16(lh) == to_int32(e);
        }
        assert uint16_as_nelem(lh) == MQN.normalize(a);
    }

    lemma normalization_post_lemma(outputs: seq<uint16>, inputs: seq<uint16>)
        requires buff_is_n_elems(inputs);
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
        && var ns1 := uint16_buff_as_n_nelems(s1);
        && var ns2 := uint16_buff_as_n_nelems(s2);
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
        && ((result == 1) <==> (MQN.l2norm_squared(uint16_buff_as_n_nelems(s1), uint16_buff_as_n_nelems(s2), |s1|) < 0x29845d6))
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
        requires buff_is_n_elems(tt0);
        requires buff_is_n_elems(c0);
        requires buff_is_n_elems(h);
        requires denormalization_inv(s2, tt0, 512);
        requires tt1 == poly_mod_product(tt0, h);
        requires poly_sub_loop_inv(tt2, tt1, c0, 512);
        requires normalization_inv(s1, tt2, 512);
        ensures (result == 1) <==> falcon_verify(
            buff_as_n_elems(c0), uint16_buff_as_n_nelems(s2), buff_as_n_elems(h));
    {
        reveal denormalization_inv();
        assert tt0 == MQN.denormalize_n_elems(uint16_buff_as_n_nelems(s2));
        assert tt1 == MQP.poly_mod(MQP.poly_mul(tt0, h), MQP.n_ideal());
        assume c0 == buff_as_n_elems(c0);
        assume h == buff_as_n_elems(h);
        assert tt2 == MQP.poly_sub(tt1, c0);
        reveal normalization_inv();
        assert uint16_buff_as_n_nelems(s1) == MQN.normalize_elems(tt2);
        assert falcon_512_i.bound() == 0x29845d6;
    }
}