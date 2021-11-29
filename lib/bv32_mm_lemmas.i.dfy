include "../arch/riscv/machine.s.dfy"
include "generic_mm_lemmas.dfy"
include "bv32_ops.dfy"

module bv32_mm_lemmas refines generic_mm_lemmas {
    import opened GBV = bv32_ops

    type uint64_view_t = dw_view_t

    predicate valid_uint64_view(
        num: uint64_view_t,
        lh: uint32, uh: uint32)
    {
        && lh == num.lh
        && uh == num.uh
    }

    lemma mul32_correct_lemma(a: uint32, b: uint32, c: uint32, d: uint32)
        requires c == uint32_mul(a, b);
        requires d == uint32_mulhu(a, b);
        ensures to_nat([c, d]) == a * b;
    {
        reveal dw_lh();
        reveal dw_uh();

        var full := a * b;
        dw_split_lemma(full);

        GBV.BVSEQ.LemmaSeqLen2([c, d]);
    }


}