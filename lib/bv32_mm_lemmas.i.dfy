include "../arch/riscv/machine.s.dfy"
include "generic_mm_lemmas.dfy"
include "bv32_ops.dfy"

module bv32_mm_lemmas refines generic_mm_lemmas {
    import opened GBV = bv32_ops
    import opened rv_machine

    type uint64_view_t = dw_view_t

    const NA : int := -1;

    const NUM_WORDS := 96;

    predicate valid_uint64_view(
        num: uint64_view_t,
        lh: uint32, uh: uint32)
    {
        && lh == num.lh
        && uh == num.uh
    }

    lemma mul32_correct_lemma(a: uint32, b: uint32, c: uint32, d: uint32)
        requires c == uint32_mul(a, b);
        requires d == uint32_mulhu(a, b);
        ensures to_nat([c, d]) == a * b;
    {
        reveal dw_lh();
        reveal dw_uh();

        var full := a * b;
        dw_split_lemma(full);

        GBV.BVSEQ.LemmaSeqLen2([c, d]);
    }

    datatype mma_vars = mma_vars(
        frame_ptr: uint32, // writable
        iter_a: iter_t,
        a_i: uint32,
        i: nat,
        // d0: uint32,
        iter_b: iter_t,
        iter_c: iter_t, // writable
        iter_n: iter_t
    )

    predicate mvar_iter_inv(mem: mem_t, iter: iter_t, address: int, index: int, value: int)
    {
        && (address >= 0 ==> iter_inv(iter, mem, address))
        && (value >= 0 ==> to_nat(iter.buff) == value)
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == NUM_WORDS
    }

    predicate mma_vars_inv(
        vars: mma_vars,
        mem: mem_t,
        n_ptr: int, n_idx: int,
        c_ptr: int, c_idx: int,
        b_ptr: int, b_idx: int,
        rsa: rsa_params)
    {
        && valid_frame_ptr(mem, vars.frame_ptr, 12)

        && mvar_iter_inv(mem, vars.iter_a, -1, vars.i, NA)
        && vars.i <= NUM_WORDS
        && (vars.i < NUM_WORDS ==> vars.iter_a.buff[vars.i] == vars.a_i)
        && mvar_iter_inv(mem, vars.iter_n, n_ptr, n_idx, rsa.M)
        && mvar_iter_inv(mem, vars.iter_c, c_ptr, c_idx, NA)
        && mvar_iter_inv(mem, vars.iter_b, b_ptr, b_idx, NA)

        && vars.iter_c.base_addr != vars.iter_a.base_addr
        && vars.iter_c.base_addr != vars.iter_n.base_addr
        && vars.iter_c.base_addr != vars.iter_b.base_addr
        && vars.iter_c.base_addr != vars.frame_ptr

        && vars.frame_ptr != vars.iter_a.base_addr
        && vars.frame_ptr != vars.iter_n.base_addr
        && vars.frame_ptr != vars.iter_b.base_addr

        && rsa_params_inv(rsa)
    }

    datatype mm_vars = mm_vars_cons(
        mm_frame_ptr: uint32, // writable
        mma_frame_ptr: uint32, // writable
        iter_a: iter_t,
        iter_b: iter_t,
        iter_c: iter_t, // writable
        iter_n: iter_t
    )

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

    function to_mma_vars(vars: mm_vars, a_i: uint32): mma_vars
    {
        mma_vars(vars.mma_frame_ptr,
            vars.iter_a, a_i, vars.iter_a.index,
            vars.iter_b, vars.iter_c, vars.iter_n)
    }

    function seq_zero(i: nat): seq<uint32>
    {
        GBV.BVSEQ.SeqZero(NUM_WORDS)
    }

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

}