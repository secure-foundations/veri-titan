include "../../../spec/arch/msp430/machine.s.dfy"
include "../../../spec/bvop/bv16_op.s.dfy"
include "../../../spec/arch/msp430/vale.i.dfy"
include "../../generic_mm_lemmas.dfy"

module bv16_mm_lemmas refines generic_mm_lemmas {
    import opened GBV = bv16_op_s
    import opened msp_machine
    import opened mem
    import opened msp_vale

    const NA : int := -1;

    const NUM_WORDS := 192;

    type uint32_view_t = dw_view_t

    predicate valid_uint32_view(
        num: uint32_view_t,
        lh: uint16, uh: uint16)
    {
        && lh == num.lh
        && uh == num.uh
    }

    predicate mvar_iter_inv(heap: heap_t, iter: iter_t, address: int, index: int, value: int)
    {
        && (address >= 0 ==> iter_inv(iter, heap, address))
        && (value >= 0 ==> to_nat(iter.buff) == value)
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == NUM_WORDS
    }
}