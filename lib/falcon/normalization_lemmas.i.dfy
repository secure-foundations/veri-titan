include "bv32_falcon_lemmas.i.dfy"
include "mq_arith_lemmas.dfy"
include "../bv16_ops.dfy"

module normalization_lemmas {
    import opened bv32_falcon_lemmas
    import opened mem
    import opened rv_machine
    import opened integers
    import opened ntt_512_params
    import opened bv32_ops
    import opened mq_arith_lemmas

    import bv16_ops

    const Q_HLAF :int := Q/2

    // const NORMaLIZED_HIGHER_INCLUSIVE :int := Q_HLAF
    // const NORMaLIZED_LOWER_INCLUSIVE :int := -Q_HLAF

    predicate int_is_normalized(e: int)
    {
        -Q_HLAF <= e <= Q_HLAF
    }

    type nelem = e: int | int_is_normalized(e)

    function normalize(e: elem): nelem
    {
        if e <= Q_HLAF then e else e as int - Q
    }

    function denormalize(e: nelem): elem
    {
        if e >= 0 then e else e + Q
    }

    predicate uint16_is_normalized(e: uint16)
    {
        int_is_normalized(bv16_ops.to_int16(e))
    }

    // bascially convert to int16, but with requires
    // DOES NOT normalize a value
    // ONLY interprets an uint16 as a normalized value
    function uint16_as_nelem(e: uint16): nelem
        requires uint16_is_normalized(e)
    {
        bv16_ops.to_int16(e)
    }

    predicate {:opaque} normalized_values(a: seq<uint16>)
        ensures normalized_values(a) ==> |a| == N.full;
    {
        && |a| == N.full
        && (forall i | 0 <= i < |a| :: uint16_is_normalized(a[i]))
    }

    function uint16_buff_as_nelems(a: seq<uint16>): (na: seq<nelem>)
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
        requires b == to_uint32(int32_rs(to_int32(a1), 31));
        requires c == uint32_and(b, Q);
        requires d == uint32_add(a1, c);
        ensures uint16_is_normalized(buff[i]);
        ensures d == denormalize(uint16_as_nelem(buff[i]));
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
            assert d == denormalize(uint16_as_nelem(a0));
        }
        else {
            assert sa0 < 0;
            assert int32_rs(to_int32(a1), 31) == -1 by { lemma_rs_by_31(to_int32(a1)); }
            lemma_uint32_and_Q(b);
            assert c == Q;
            assert d == sa0 + Q;
            assert d == denormalize(uint16_as_nelem(a0));
        }
    }

    predicate {:opaque} denormalization_inv(nv: seq<uint16>, dnv: seq<uint16>, i: nat)
        requires normalized_values(nv);
        requires buff_is_nsized(dnv);
    {
        && reveal normalized_values();
        && i <= N.full
        && (forall j | 0 <= j < i :: dnv[j] == denormalize(uint16_as_nelem(nv[j])))
    }

    lemma denormalization_pre_lemma(nv: seq<uint16>, dnv: seq<uint16>)
        requires normalized_values(nv);
        requires buff_is_nsized(dnv);
        ensures denormalization_inv(nv, dnv, 0);
    {
        reveal denormalization_inv();
    }

    lemma denormalization_peri_lemma(buff: seq<uint16>, dnv: seq<uint16>, i: nat, a1: uint32, b: uint32, c: uint32, d: uint32)
        requires normalized_values(buff);
        requires buff_is_nsized(dnv);
        requires denormalization_inv(buff, dnv, i);
        requires i < |buff|;
        requires a1 == uint16_sign_ext(buff[i]);
        requires b == to_uint32(int32_rs(to_int32(a1), 31));
        requires c == uint32_and(b, Q);
        requires d == uint32_add(a1, c);
        ensures uint16_is_normalized(buff[i]);
        ensures d == denormalize(uint16_as_nelem(buff[i]));
        ensures buff_is_nsized(dnv[i := d]);
        ensures denormalization_inv(buff, dnv[i := d], i + 1);
    {
        reveal denormalization_inv();
        reveal normalized_values();
        denormalize_lemma(buff, i, a1, b, c, d);
        var dnv' := dnv[i := d];
        forall j | 0 <= j <= i
            ensures dnv'[j] == denormalize(uint16_as_nelem(buff[j]))
        {
        } 
        reveal buff_is_nsized();
    }
}