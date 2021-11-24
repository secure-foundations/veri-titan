include "mont_mul_add_lemmas.i.dfy"

module mont_mul_lemmas {
    import opened bv_ops
    import opened rsa_ops
    import opened rv_machine

    import opened BASE_32_Seq
    import opened Mul
    import Power2
    import Power
    import opened DivMod
    
    import opened mont_mul_add_lemmas

    datatype mm_vars = mm_vars(
        mm_frame_ptr: uint32, // writable
        mma_frame_ptr: uint32, // writable
        iter_a: iter_t,
        iter_b: iter_t,
        iter_c: iter_t, // writable
        iter_n: iter_t
    )

    function to_mma_vars(vars: mm_vars, a_i: uint32): mma_vars
    {
        mma_vars(vars.mma_frame_ptr,
            vars.iter_a, a_i, vars.iter_a.index,
            vars.iter_b, vars.iter_c, vars.iter_n)
    }

    predicate mm_vars_inv(
        vars: mm_vars,
        mem: mem_t,
        a_ptr: int, a_idx: int,
        n_ptr: int, n_idx: int,
        c_ptr: int, c_idx: int,
        b_ptr: int, b_idx: int,
        rsa: rsa_params)
    {
        && mvar_iter_inv(mem, vars.iter_a, a_ptr, a_idx, NA)
        && var a_i := if 0 <= a_idx < NUM_WORDS then vars.iter_a.buff[a_idx] else 0;
        && var mma := to_mma_vars(vars, a_i);
        && mma_vars_inv(mma, mem, n_ptr, n_idx, c_ptr, c_idx, b_ptr, b_idx, rsa)
        && valid_frame_ptr(mem, vars.mm_frame_ptr, 12)
        && vars.mm_frame_ptr != vars.mma_frame_ptr
        && vars.mm_frame_ptr != vars.iter_a.base_addr
        && vars.mm_frame_ptr != vars.iter_b.base_addr
        && vars.mm_frame_ptr != vars.iter_c.base_addr
        && vars.mm_frame_ptr != vars.iter_n.base_addr
    }
}