include "../../arch/riscv/machine.s.dfy"
include "../../lib/signed_bv_ops.dfy"
include "../../std_lib/src/Collections/Sequences/LittleEndianNat.dfy"

module BASE_32_Seq refines LittleEndianNat {
    import opened bv_ops
    
    function method BASE(): nat { BASE_32 }
}

module rsa_ops {
    import opened bv_ops
    import opened rv_machine

    import opened DivMod
    import opened Power
    import opened BASE_32_Seq
    import opened Seq

    function to_nat(xs: seq<uint32>): nat
    {
        ToNatRight(xs)
    }

    function seq_subb(xs: seq<uint32>, ys: seq<uint32>): (seq<uint32>, uint1)
        requires |xs| == |ys|
    {
        SeqSub(xs, ys)
    }

    /* to_nat definions & lemmas */

     lemma to_nat_lemma_0(xs: seq<uint32>)
         requires |xs| == 1
         ensures ToNatRight(xs) == xs[0]
     {
         reveal ToNatRight();
         assert BASE() == 0x1_00000000;
     }

    lemma to_nat_lemma_1(xs: seq<uint32>)
        requires |xs| == 2
        ensures ToNatRight(xs) == xs[0] + xs[1] * BASE_32
    {
        LemmaSeqLen2(xs);
    }
}
