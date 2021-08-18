include "vt_consts.dfy"
include "bv_ops.dfy"
include "vt_ops.dfy"
include "../libraries/src/NonlinearArithmetic/Power.dfy"
include "../libraries/src/NonlinearArithmetic/DivMod.dfy"
include "../libraries/src/Collections/Sequences/NatSeq.dfy"

module BASE_256_Seq refines NatSeq {
    import NT = NativeTypes
    
    function method BOUND(): nat { NT.BASE_256 }
}

module rsa_ops {
    import opened vt_consts
    import opened bv_ops
    import opened vt_ops
    import opened Power
    import opened DivMod 
    import NT = NativeTypes
    import opened BASE_256_Seq

    // lemma lsw_cong_lemma(xs: seq<uint>)
    //     requires |xs| >= 1;
    //     ensures cong_B256(ToNat(xs), xs[0]);

    lemma uint512_view_lemma(num: uint512_view_t)
        ensures num.full
            == ToNat([num.lh, num.uh])
            == num.lh + num.uh * NT.BASE_256;
    {
        reveal uint512_lh();
        reveal uint512_uh();
        LemmaSeqLen2([num.lh, num.uh]);
    }

    // function seq_zero(len: nat): (zs: seq<uint>)
    //     ensures |zs| == len

    // lemma seq_zero_to_nat_lemma(len: nat)
    //     ensures ToNat(seq_zero(len)) == 0

    // lemma to_nat_bound_lemma(xs: seq<uint>)
    //     ensures ToNat(xs) < pow_B256(|xs|)

    // lemma to_nat_zero_prepend_lemma (xs: seq<uint>)
    //   ensures ToNat([0] + xs) == ToNat(xs) * NT.BASE_256

    // lemma to_nat_prefix_lemma(xs: seq<uint>, i: nat)
    //     requires 0 <= i < |xs|;
    //     ensures ToNat(xs[..i]) + ToNat(xs[i..]) * pow_B256(i) == ToNat(xs);

    // lemma to_nat_zero_extend_lemma(xs': seq<uint>, xs: seq<uint>) 
    //     requires |xs'| < |xs|
    //     requires var len' := |xs'|;
    //         && xs[..len'] == xs'
    //         && xs[len'.. ] == seq(|xs| - len', i => 0)
    //     ensures ToNat(xs') == ToNat(xs);

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
        && rsa.SIG < rsa.M

        && rsa.R == Pow(NT.BASE_256, NUM_WORDS)

        && rsa.RR < rsa.M
        && IsModEquivalent(rsa.RR, rsa.R * rsa.R, rsa.M)

        && rsa.R_INV == Pow(rsa.B256_INV, NUM_WORDS)
        && IsModEquivalent(rsa.R_INV * rsa.R, 1, rsa.M)

        && IsModEquivalent(NT.BASE_256 * rsa.B256_INV, 1, rsa.M)
    }

    datatype mvars = mvars(
        x_it: iter_t,
        y_it: iter_t,

        m_it: iter_t,
        m0d_it: iter_t,
        rr_it: iter_t,
        sig_it: iter_t,
        rsa: rsa_params)

    predicate mvars_iter_init(iter: iter_t, wmem: wmem_t, address: int, value: int)
    {
        && (address != NA ==> iter_inv(iter, wmem, address))
        && (value != NA ==> ToNat(iter.buff) == value)
            && iter.index == 0
        && |iter.buff| == NUM_WORDS
    }

    predicate m0d_it_inv(iter: iter_t, wmem: wmem_t, address: int)
    {
        && (address != NA ==> iter_inv(iter, wmem, address))
        && iter.index == 0
        && |iter.buff| == 1
    }

    predicate mvars_inv(
        vars: mvars,
        wmem: wmem_t,
        x_ptr: int,
        y_ptr: int,
        m_ptr: int,
        m0d_ptr: int,
        rr_ptr: int,
        sig_ptr: int)
    {
        && rsa_params_inv(vars.rsa)

        && mvars_iter_init(vars.x_it, wmem, x_ptr, NA)
        && mvars_iter_init(vars.y_it, wmem, y_ptr, NA)
        && mvars_iter_init(vars.sig_it, wmem, sig_ptr, vars.rsa.SIG)
        && mvars_iter_init(vars.m_it, wmem, m_ptr, vars.rsa.M)
        && mvars_iter_init(vars.rr_it, wmem, rr_ptr, vars.rsa.RR)

        && m0d_it_inv(vars.m0d_it, wmem, m0d_ptr)
        && vars.m0d_it.buff[0] == vars.rsa.M0D
    }

    predicate mvars_init(
        vars: mvars,
        xmem: xmem_t,
        wmem: wmem_t,
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

        && mvars_inv(vars, wmem, NA, NA, m_ptr, m0d_ptr, rr_ptr, sig_ptr)
        && wmem_base_addr_valid(wmem, out_ptr, NUM_WORDS)

        && out_ptr != m0d_ptr
        && out_ptr != rr_ptr
        && out_ptr != m_ptr
        && out_ptr != sig_ptr
    }
}
