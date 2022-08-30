include "../arch/riscv/machine.s.dfy"
include "DivModNeg.dfy"
include "bv32_op_s.dfy"

module sub_mod_nl_lemmas {

    import opened integers
    import opened bv32_op_s
    import opened bv32_op_s.BVSEQ

    import opened DivModNeg


    lemma div_negative_one(a: nat)
        requires a > 1
        ensures -1 / a == -1
    {
    }
}
