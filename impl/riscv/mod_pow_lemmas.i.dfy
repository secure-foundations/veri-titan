include "mont_mul_lemmas.i.dfy"

module mod_pow_lemmas {
    import opened bv_ops
    import opened rsa_ops
    import opened rv_machine

    import opened BASE_32_Seq
    import opened Mul
    import Power2
    import opened Power
    import opened DivMod
    
    import opened mont_mul_add_lemmas
    import opened mont_mul_lemmas

    datatype mp_vars = mp_vars(
        mp_frame_ptr: uint32, // writable
        mm_frame_ptr: uint32, // writable
        mma_frame_ptr: uint32, // writable
        iter_rr: iter_t, 
        iter_n: iter_t,
        iter_in: iter_t,
        iter_ar: iter_t, // writable
        iter_aar: iter_t, // writable
        iter_out: iter_t // writable
    )

    predicate mp_vars_inv(
        vars: mp_vars,
        mem: mem_t,
        rr_ptr: nat,
        n_ptr: nat,
        in_ptr: nat,
        ar_ptr: nat,
        aar_ptr: nat,
        out_ptr: nat,
        rsa: rsa_params)
    {
        && valid_frame_ptr(mem, vars.mp_frame_ptr, 8)
        && valid_frame_ptr(mem, vars.mm_frame_ptr, 8)
        && valid_frame_ptr(mem, vars.mma_frame_ptr, 12)

        && mvar_iter_inv(mem, vars.iter_rr, rr_ptr, 0, rsa.RR)
        && mvar_iter_inv(mem, vars.iter_n, n_ptr, 0, rsa.M)
        && mvar_iter_inv(mem, vars.iter_in, in_ptr, 0, rsa.SIG)
        && mvar_iter_inv(mem, vars.iter_ar, ar_ptr, 0, NA)
        && mvar_iter_inv(mem, vars.iter_aar, aar_ptr, 0, NA)
        && mvar_iter_inv(mem, vars.iter_out, out_ptr, 0, NA)

        && vars.iter_ar.base_addr != vars.iter_rr.base_addr
        && vars.iter_ar.base_addr != vars.iter_n.base_addr
        && vars.iter_ar.base_addr != vars.iter_in.base_addr
        && vars.iter_ar.base_addr != vars.iter_aar.base_addr
        && vars.iter_ar.base_addr != vars.iter_out.base_addr
        && vars.iter_ar.base_addr != vars.mp_frame_ptr
        && vars.iter_ar.base_addr != vars.mm_frame_ptr
        && vars.iter_ar.base_addr != vars.mma_frame_ptr

        && vars.iter_aar.base_addr != vars.iter_rr.base_addr
        && vars.iter_aar.base_addr != vars.iter_n.base_addr
        && vars.iter_aar.base_addr != vars.iter_in.base_addr
        && vars.iter_aar.base_addr != vars.iter_out.base_addr
        && vars.iter_aar.base_addr != vars.mp_frame_ptr
        && vars.iter_aar.base_addr != vars.mm_frame_ptr
        && vars.iter_aar.base_addr != vars.mma_frame_ptr

        && vars.iter_out.base_addr != vars.iter_rr.base_addr
        && vars.iter_out.base_addr != vars.iter_n.base_addr
        && vars.iter_out.base_addr != vars.iter_in.base_addr
        && vars.iter_out.base_addr != vars.mp_frame_ptr
        && vars.iter_out.base_addr != vars.mm_frame_ptr
        && vars.iter_out.base_addr != vars.mma_frame_ptr

        && vars.mp_frame_ptr != vars.iter_rr.base_addr
        && vars.mp_frame_ptr != vars.iter_n.base_addr
        && vars.mp_frame_ptr != vars.iter_in.base_addr
        && vars.mp_frame_ptr != vars.mm_frame_ptr
        && vars.mp_frame_ptr != vars.mma_frame_ptr

        && vars.mm_frame_ptr != vars.iter_rr.base_addr
        && vars.mm_frame_ptr != vars.iter_n.base_addr
        && vars.mm_frame_ptr != vars.iter_in.base_addr
        && vars.mm_frame_ptr != vars.mma_frame_ptr

        && vars.mma_frame_ptr != vars.iter_rr.base_addr
        && vars.mma_frame_ptr != vars.iter_n.base_addr
        && vars.mma_frame_ptr != vars.iter_in.base_addr

        && rsa_params_inv(rsa)
    }

    predicate modexp_var_inv(a: seq<uint32>, rsa: rsa_params, i: nat)
        requires rsa_params_inv(rsa)
    {
        LemmaPowPositiveAuto();
        && IsModEquivalent(to_nat(a), Pow(rsa.SIG, Pow(4, i)) * rsa.R, rsa.M)
    }

    lemma modexp_var_inv_pre_lemma(
        a_view: seq<uint32>,
        rr: seq<uint32>,
        sig: seq<uint32>,
        rsa: rsa_params)

    requires montmul_inv(a_view, sig, NUM_WORDS, rr, rsa);
    requires to_nat(rr) == rsa.RR;
    requires to_nat(sig) == rsa.SIG;
    ensures modexp_var_inv(a_view, rsa, 0);

    lemma modexp_var_inv_peri_lemma(
        ar: seq<uint32>,
        aar: seq<uint32>,
        aaaar: seq<uint32>,
        i: nat,
        rsa: rsa_params)

        requires montmul_inv(aar, ar, NUM_WORDS, ar, rsa);
        requires montmul_inv(aaaar, aar, NUM_WORDS, aar, rsa);
        requires modexp_var_inv(ar, rsa, i);
        ensures modexp_var_inv(aaaar, rsa, i + 1);

    lemma modexp_var_inv_post_lemma(
        a_view: seq<uint32>,
        next_a_view: seq<uint32>,
        sig: seq<uint32>,
        rsa: rsa_params)

        requires montmul_inv(next_a_view, a_view, NUM_WORDS, sig, rsa);
        requires modexp_var_inv(a_view, rsa, 8);
        ensures IsModEquivalent(to_nat(next_a_view), Pow(to_nat(sig), 65537), rsa.M);

    lemma modexp_var_correct_lemma(
        raw_val: nat,
        adjusted_val: nat,
        carry: bool,
        rsa: rsa_params)

    requires rsa_params_inv(rsa);
    requires raw_val < rsa.SIG + rsa.M;
    requires IsModEquivalent(raw_val, Pow(rsa.SIG, 65537), rsa.M);
    requires carry ==> raw_val < rsa.M;
    requires !carry ==> raw_val - rsa.M == adjusted_val;

    ensures carry ==> raw_val == Pow(rsa.SIG, 65537) % rsa.M;
    ensures !carry ==> adjusted_val == Pow(rsa.SIG, 65537) % rsa.M;

    function mod(a: nat, m: nat): int
        requires m != 0;
    {
        a % m
    }
}