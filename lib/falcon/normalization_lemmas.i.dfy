include "bv32_falcon_lemmas.i.dfy"
include "../bv16_ops.dfy"

module normalization_lemmas {
    import opened bv32_falcon_lemmas
    import opened mem
    import opened rv_machine
    import opened integers
    import opened ntt_512_params

    import bv16_ops

    predicate {:opaque} buff_normlized(a: seq<uint16>)
        ensures buff_is_nsized(a) ==> |a| == N.full;
    {
        && (|a| == N.full)
        && (forall i | 0 <= i < N.full :: bv16_ops.to_int16(a[i]) < Q)
    }

    predicate normlized_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(iter, heap, if address >= 0 then address else iter.cur_ptr())
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && buff_normlized(iter.buff)
    }
}