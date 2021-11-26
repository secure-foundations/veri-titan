include "mont_mul_lemmas.i.dfy"

module mod_pow_lemmas {
    import opened bv_ops
    import opened rsa_ops
    import opened rv_machine

    import opened BASE_32_Seq
    import opened Mul
    import Power2
    import Power
    import opened DivMod
    
    import opened mont_mul_lemmas

    datatype mp_vars = mp_vars(
        me_frame_ptr: uint32, // writable
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
        && mvar_iter_inv(mem, vars.iter_rr, rr_ptr, 0, rsa.RR)
        && mvar_iter_inv(mem, vars.iter_n, n_ptr, 0, rsa.M)
        && mvar_iter_inv(mem, vars.iter_in, in_ptr, 0, rsa.M)
        && mvar_iter_inv(mem, vars.iter_ar, ar_ptr, 0, NA)
        && mvar_iter_inv(mem, vars.iter_aar, aar_ptr, 0, NA)
        && mvar_iter_inv(mem, vars.iter_out, out_ptr, 0, NA)

        && vars.iter_ar.base_addr != vars.iter_rr.base_addr
        && vars.iter_ar.base_addr != vars.iter_n.base_addr
        && vars.iter_ar.base_addr != vars.iter_in.base_addr
        && vars.iter_ar.base_addr != vars.iter_aar.base_addr
        && vars.iter_ar.base_addr != vars.iter_out.base_addr
        && vars.iter_ar.base_addr != vars.me_frame_ptr
        && vars.iter_ar.base_addr != vars.mm_frame_ptr
        && vars.iter_ar.base_addr != vars.mma_frame_ptr

        && vars.iter_aar.base_addr != vars.iter_rr.base_addr
        && vars.iter_aar.base_addr != vars.iter_n.base_addr
        && vars.iter_aar.base_addr != vars.iter_in.base_addr
        && vars.iter_aar.base_addr != vars.iter_out.base_addr
        && vars.iter_aar.base_addr != vars.me_frame_ptr
        && vars.iter_aar.base_addr != vars.mm_frame_ptr
        && vars.iter_aar.base_addr != vars.mma_frame_ptr

        && vars.iter_out.base_addr != vars.iter_rr.base_addr
        && vars.iter_out.base_addr != vars.iter_n.base_addr
        && vars.iter_out.base_addr != vars.iter_in.base_addr
        && vars.iter_out.base_addr != vars.me_frame_ptr
        && vars.iter_out.base_addr != vars.mm_frame_ptr
        && vars.iter_out.base_addr != vars.mma_frame_ptr

        && vars.me_frame_ptr != vars.iter_rr.base_addr
        && vars.me_frame_ptr != vars.iter_n.base_addr
        && vars.me_frame_ptr != vars.iter_in.base_addr
        && vars.me_frame_ptr != vars.mm_frame_ptr
        && vars.me_frame_ptr != vars.mma_frame_ptr

        && vars.mm_frame_ptr != vars.iter_rr.base_addr
        && vars.mm_frame_ptr != vars.iter_n.base_addr
        && vars.mm_frame_ptr != vars.iter_in.base_addr
        && vars.mm_frame_ptr != vars.mma_frame_ptr

        && vars.mma_frame_ptr != vars.iter_rr.base_addr
        && vars.mma_frame_ptr != vars.iter_n.base_addr
        && vars.mma_frame_ptr != vars.iter_in.base_addr
    }
}