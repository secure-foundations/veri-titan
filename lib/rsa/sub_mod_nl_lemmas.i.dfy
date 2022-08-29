include "../arch/riscv/machine.s.dfy"
include "DivModNeg.dfy"
include "bv32_ops.dfy"

module sub_mod_nl_lemmas {

    import opened integers
    import opened bv32_ops
    import opened bv32_ops.BVSEQ

    import opened DivModNeg


    lemma div_negative_one(a: nat)
        requires a > 1
        ensures -1 / a == -1
    {
    }
}
