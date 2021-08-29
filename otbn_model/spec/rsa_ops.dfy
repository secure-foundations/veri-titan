include "vt_consts.dfy"
include "bv_ops.dfy"
include "vt_ops.dfy"
include "../libraries/src/Collections/Sequences/NatSeq.dfy"

module BASE_256_Seq refines NatSeq {
    import opened NativeTypes
    
    function method BOUND(): nat { BASE_256 }
}

module rsa_ops {
    import opened vt_consts
    import opened bv_ops
    import opened vt_ops
    import opened vt_mem

    import opened DivMod
    import opened Power
    import opened NativeTypes
    import opened BASE_256_Seq


/* to_nat definions & lemmas */

    // function to_nat(xs: seq<uint256>): nat
    // {
    //     ToNat(xs)
    // }

    // lemma to_nat_lemma_0(xs: seq<uint256>)
    //     requires |xs| == 1
    //     ensures to_nat(xs) == xs[0]
    // {
    //     reveal to_nat();
    //     reveal power();
    // }

    // lemma to_nat_lemma_1(xs: seq<uint256>)
    //     requires |xs| == 2
    //     ensures to_nat(xs) == xs[0] + xs[1] * BASE_256
    // {
    //     reveal to_nat();
    //     to_nat_lemma_0(xs[..1]);
    //     reveal power();
    // }

    // // unstable
    // lemma lsw_cong_lemma(xs: seq<uint256>)
    //     requires |xs| >= 1;
    //     ensures cong_B256(to_nat(xs), xs[0]);
    // {
    //     if |xs| == 1 {
    //         to_nat_lemma_0(xs);
    //         reveal cong();
    //     } else {
    //         assert cong_B256(to_nat(xs), xs[0]) by {
    //             var len' := |xs| - 1;
    //             var xs' := xs[..len'];

    //             assert cong_B256(xs[len'] * pow_B256(len'), 0) by {
    //                 reveal cong();
    //                 power_mod_lemma_1(BASE_256, len');
    //                 cong_mul_lemma_1(pow_B256(len'), 0, xs[len'], BASE_256);
    //             }

    //             calc ==> {
    //                 true;
    //                     { reveal to_nat(); reveal cong(); }
    //                 cong_B256(to_nat(xs), to_nat(xs') + xs[len'] * pow_B256(len'));
    //                     { cong_add_compose_lemma(to_nat(xs), to_nat(xs'), xs[len'] * pow_B256(len'), 0, BASE_256); }
    //                 cong_B256(to_nat(xs), to_nat(xs'));
    //                     {
    //                        lsw_cong_lemma(xs');
    //                        assert xs'[0] == xs[0];
    //                        reveal cong();
    //                     }
    //                 cong_B256(to_nat(xs), xs[0]);
    //             }
    //             assert cong_B256(to_nat(xs), xs[0]);
    //         }
    //     }

    // }

    lemma uint512_view_lemma(num: uint512_view_t)
        ensures num.full
            == ToNat([num.lh, num.uh])
            == num.lh + num.uh * BASE_256;
    {
        reveal uint512_lh();
        reveal uint512_uh();
        LemmaSeqLen2([num.lh, num.uh]);
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
        B256_INV: nat)

    predicate rsa_params_inv(rsa: rsa_params)
    {
        // E0 is derived from the exponent E
        && rsa.E == Pow(2, rsa.E0) + 1

        // modulo is none zero
        && rsa.M != 0
        && cong_B256(rsa.M0D * rsa.M, -1)

        // signature
        && 0 < rsa.SIG < rsa.M

        && rsa.R == Pow(BASE_256, NUM_WORDS)

        && rsa.RR < rsa.M
        && IsModEquivalent(rsa.RR, rsa.R * rsa.R, rsa.M)

        && rsa.R_INV == Pow(rsa.B256_INV, NUM_WORDS)
        && IsModEquivalent(rsa.R_INV * rsa.R, 1, rsa.M)

        && IsModEquivalent(BASE_256 * rsa.B256_INV, 1, rsa.M)
    }

    datatype mvars = mvars(
        x_it: iter_t,
        y_it: iter_t,

        m_it: iter_t,
        m0d_it: iter_t,
        rr_it: iter_t,
        sig_it: iter_t,
        rsa: rsa_params)

    predicate mvars_iter_init(iter: iter_t, heap: heap_t, address: int, value: int)
    {
        && (address >= 0 ==> iter_inv(iter, heap, address))
        && (value >= 0 ==> ToNat(iter.buff) == value)
        && iter.index == 0
        && |iter.buff| == NUM_WORDS
    }

    predicate m0d_it_inv(iter: iter_t, heap: heap_t, address: int)
    {
        && (address >= 0 ==> iter_inv(iter, heap, address))
        && iter.index == 0
        && |iter.buff| == 1
    }

    predicate mvars_inv(
        vars: mvars,
        heap: heap_t,
        x_ptr: int,
        y_ptr: int,
        m_ptr: int,
        m0d_ptr: int,
        rr_ptr: int,
        sig_ptr: int)
    {
        && rsa_params_inv(vars.rsa)

        && mvars_iter_init(vars.x_it, heap, x_ptr, NA)
        && mvars_iter_init(vars.y_it, heap, y_ptr, NA)
        && mvars_iter_init(vars.sig_it, heap, sig_ptr, vars.rsa.SIG)
        && mvars_iter_init(vars.m_it, heap, m_ptr, vars.rsa.M)
        && mvars_iter_init(vars.rr_it, heap, rr_ptr, vars.rsa.RR)

        && m0d_it_inv(vars.m0d_it, heap, m0d_ptr)
        && vars.m0d_it.buff[0] == vars.rsa.M0D
    }

    predicate mvars_init(
        vars: mvars,
        xmem: xmem_t,
        heap: heap_t,
        m_ptr: uint32,
        m0d_ptr: uint32,
        rr_ptr: uint32,
        sig_ptr: uint32,
        out_ptr: uint32)
    {
        && rsa_params_inv(vars.rsa)

        && xmem_addr_mapped(xmem, 0, vars.rsa.E0)
        && xmem_addr_mapped(xmem, 4, NUM_WORDS)
        && xmem_addr_mapped(xmem, 16, m_ptr)
        && xmem_addr_mapped(xmem, 8, m0d_ptr)
        && xmem_addr_mapped(xmem, 12, rr_ptr)
        && xmem_addr_mapped(xmem, 20, sig_ptr)
        && xmem_addr_mapped(xmem, 28, out_ptr)

        && mvars_inv(vars, heap, NA, NA, m_ptr, m0d_ptr, rr_ptr, sig_ptr)
        && heap_base_addr_valid(heap, out_ptr)
        && |heap[out_ptr]| == NUM_WORDS

        && out_ptr != m0d_ptr
        && out_ptr != rr_ptr
        && out_ptr != m_ptr
        && out_ptr != sig_ptr
    }
}
