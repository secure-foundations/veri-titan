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

    function to_nat(xs: seq<BASE_32_Seq.uint>): nat
    {
        assert BASE() == BASE_32;
        BASE_32_Seq.ToNatRight(xs)
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

    /* rsa/mm definions & lemmas */
   datatype rsa_params = rsa_params(
        M: nat, 
        M0D: uint,
        R: nat,
        RR: nat,
        R_INV: nat,
        E: nat,
        E0: uint32,
        SIG: nat,
        B32_INV: nat)

    predicate rsa_params_inv(rsa: rsa_params)
    {
        // E0 is derived from the exponent E
        && rsa.E == Pow(2, rsa.E0) + 1

        // modulo is none zero
        && rsa.M != 0
        && cong_B32(rsa.M0D * rsa.M, -1)

        // signature
        && 0 < rsa.SIG < rsa.M

        && rsa.R == Pow(BASE_32, NUM_WORDS)

        && rsa.RR < rsa.M
        && IsModEquivalent(rsa.RR, rsa.R * rsa.R, rsa.M)

        && rsa.R_INV == Pow(rsa.B32_INV, NUM_WORDS)
        && IsModEquivalent(rsa.R_INV * rsa.R, 1, rsa.M)

        && IsModEquivalent(BASE_32 * rsa.B32_INV, 1, rsa.M)
    }

    datatype mvars = mvars(
        x_it: iter_t,
        y_it: iter_t,

        m_it: iter_t,
        rr_it: iter_t,
        sig_it: iter_t,
        rsa: rsa_params)

    predicate mvar_iter_inv(mem: mem_t, iter: iter_t, address: int, index: int, value: int)
    {
        && (address >= 0 ==> iter_inv(iter, mem, address))
        && (value >= 0 ==> to_nat(iter.buff) == value)
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == NUM_WORDS
    }

    // predicate mvars_inv(
    //     vars: mvars,
    //     mem: mem_t,
    //     x_ptr: int,
    //     y_ptr: int,
    //     m_ptr: int,
    //     rr_ptr: int,
    //     sig_ptr: int)
    // {
    //     && rsa_params_inv(vars.rsa)

    //     && mvars_iter_init(vars.x_it, mem, x_ptr, NA)
    //     && mvars_iter_init(vars.y_it, mem, y_ptr, NA)
    //     && mvars_iter_init(vars.sig_it, mem, sig_ptr, vars.rsa.SIG)
    //     && mvars_iter_init(vars.m_it, mem, m_ptr, vars.rsa.M)
    //     && mvars_iter_init(vars.rr_it, mem, rr_ptr, vars.rsa.RR)
    // }

    // predicate mvars_init(
    //     vars: mvars,
    //     mem: mem_t,
    //     m_ptr: uint32,
    //     rr_ptr: uint32,
    //     sig_ptr: uint32,
    //     out_ptr: uint32)
    // {
    //     && rsa_params_inv(vars.rsa)

    //     && mvars_inv(vars, mem, NA, NA, m_ptr, rr_ptr, sig_ptr)


    // }
}
