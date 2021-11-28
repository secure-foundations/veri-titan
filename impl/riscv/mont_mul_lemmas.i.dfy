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

    datatype mm_vars = mm_vars_cons(
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
        a_ptr: int, a_idx: nat,
        n_ptr: int, n_idx: int,
        c_ptr: int, c_idx: int,
        b_ptr: int, b_idx: int,
        rsa: rsa_params)
    {
        && valid_frame_ptr(mem, vars.mm_frame_ptr, 8)
        && valid_frame_ptr(mem, vars.mma_frame_ptr, 12)

        && mvar_iter_inv(mem, vars.iter_a, a_ptr, a_idx, NA)
        && mvar_iter_inv(mem, vars.iter_c, c_ptr, c_idx, NA)
        && mvar_iter_inv(mem, vars.iter_b, b_ptr, b_idx, NA)
        && mvar_iter_inv(mem, vars.iter_n, n_ptr, n_idx, rsa.M)

        && vars.iter_c.base_addr != vars.iter_a.base_addr
        && vars.iter_c.base_addr != vars.iter_n.base_addr
        && vars.iter_c.base_addr != vars.iter_b.base_addr
        && vars.iter_c.base_addr != vars.mma_frame_ptr

        && vars.mm_frame_ptr != vars.mma_frame_ptr
        && vars.mm_frame_ptr != vars.iter_a.base_addr
        && vars.mm_frame_ptr != vars.iter_b.base_addr
        && vars.mm_frame_ptr != vars.iter_c.base_addr
        && vars.mm_frame_ptr != vars.iter_n.base_addr

        && vars.mma_frame_ptr != vars.iter_a.base_addr
        && vars.mma_frame_ptr != vars.iter_n.base_addr
        && vars.mma_frame_ptr != vars.iter_b.base_addr

        && rsa_params_inv(rsa)
    }

    lemma montmul_inv_lemma_0(
        a: seq<uint32>,
        x: seq<uint32>, 
        y: seq<uint32>, 
        rsa: rsa_params)

        requires |a| == |x| == |y| == NUM_WORDS;
        requires a == SeqZero(NUM_WORDS);
        requires rsa_params_inv(rsa);
        ensures montmul_inv(a, x, 0, y, rsa);

    lemma montmul_inv_lemma_1(
        a_view: seq<uint32>,
        x: seq<uint32>,
        y: seq<uint32>,
        rsa: rsa_params)
    
        requires montmul_inv(a_view, x, NUM_WORDS, y, rsa);
        ensures IsModEquivalent(to_nat(a_view), to_nat(x) * to_nat(y) * rsa.R_INV, rsa.M);

}