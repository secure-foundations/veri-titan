include "../arch/riscv/machine.s.dfy"
include "generic_mm_lemmas.dfy"
include "bv32_ops.dfy"
include "sub_mod_nl_lemmas.i.dfy"

module bv32_mm_lemmas refines generic_mm_lemmas {
    import opened GBV = bv32_ops
    import opened rv_machine
    import opened sub_mod_nl_lemmas

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

    lemma {:induction A, i} cmp_sufficient_lemma(A: seq<uint32>, B: seq<uint32>, i: nat)
        requires 0 <= i < |A| == |B|;
        requires forall j :: i < j < |A| ==> (A[j] == B[j]);
        ensures A[i] > B[i] ==> (to_nat(A) > to_nat(B));
        ensures A[i] < B[i] ==> (to_nat(A) < to_nat(B));
    {
        var n := |A|;
        if n != 0 {
            if i == n - 1 {
                if A[n-1] > B[n-1] {
                    GBV.BVSEQ.LemmaSeqMswInequality(B, A);
                } else if A[n-1] < B[n-1] {
                    GBV.BVSEQ.LemmaSeqMswInequality(A, B);
                }
            } else {
                var n := |A|;
                var A' := A[..n-1];
                var B' := B[..n-1];

                calc ==> {
                    A[i] > B[i];
                    {
                        cmp_sufficient_lemma(A', B', i);
                    }
                    to_nat(A') > to_nat(B');
                    {
                        GBV.BVSEQ.LemmaSeqPrefix(A, n-1);
                        GBV.BVSEQ.LemmaSeqPrefix(B, n-1);
                    }
                    to_nat(A[..n-1]) > to_nat(B[..n-1]);
                    {
                      assert A[n-1] * Pow(BASE(), n-1) == B[n-1] * Pow(BASE(), n-1);
                    }
                    to_nat(A[..n-1]) + A[n-1] * Pow(BASE(), n-1) > to_nat(B[..n-1]) + B[n-1] * Pow(BASE(), n-1);
                    {
                      assert A[..n-1] + [A[n-1]] == A;
                      assert B[..n-1] + [B[n-1]] == B;
                    }
                    to_nat(A[..n-1]) + to_nat(A[n-1..]) * Pow(BASE(), n-1) > to_nat(B[..n-1]) + to_nat(B[n-1..]) * Pow(BASE(), n-1);
                    {
                        GBV.BVSEQ.LemmaSeqPrefix(A, n-1);
                        GBV.BVSEQ.LemmaSeqPrefix(B, n-1);
                        assert to_nat(A[..n-1]) + to_nat(A[n-1..]) * Pow(BASE(), n-1) == to_nat(A);
                        assert to_nat(B[..n-1]) + to_nat(B[n-1..]) * Pow(BASE(), n-1) == to_nat(B);
                    }
                    to_nat(A) > to_nat(B);
                }
                assert A[n-1] > B[n-1] ==> (to_nat(A) > to_nat(B));

                calc ==> {
                    A[i] < B[i];
                    {
                      cmp_sufficient_lemma(A', B', i);
                    }
                    to_nat(A') < to_nat(B');
                    {
                        GBV.BVSEQ.LemmaSeqPrefix(A, n-1);
                        GBV.BVSEQ.LemmaSeqPrefix(B, n-1);
                    }
                    to_nat(A[..n-1]) < to_nat(B[..n-1]);
                    {
                      assert A[n-1] * Pow(BASE(), n-1) == B[n-1] * Pow(BASE(), n-1);
                    }
                    to_nat(A[..n-1]) + A[n-1] * Pow(BASE(), n-1) < to_nat(B[..n-1]) + B[n-1] * Pow(BASE(), n-1);
                    {
                      assert A[..n-1] + [A[n-1]] == A;
                      assert B[..n-1] + [B[n-1]] == B;
                    }
                    to_nat(A[..n-1]) + to_nat(A[n-1..]) * Pow(BASE(), n-1) < to_nat(B[..n-1]) + to_nat(B[n-1..]) * Pow(BASE(), n-1);
                    {
                        GBV.BVSEQ.LemmaSeqPrefix(A, n-1);
                        GBV.BVSEQ.LemmaSeqPrefix(B, n-1);
                        assert to_nat(A[..n-1]) + to_nat(A[n-1..]) * Pow(BASE(), n-1) == to_nat(A);
                        assert to_nat(B[..n-1]) + to_nat(B[n-1..]) * Pow(BASE(), n-1) == to_nat(B);
                    }
                    to_nat(A) < to_nat(B);
                }
                assert A[n-1] < B[n-1] ==> (to_nat(A) < to_nat(B));
            }
        }
    }

    function uint32_to_bool(x: uint32) : bool
    {
        if x == 0 then false else true
    }

    function uint32_to_uint1(x: uint32) : uint1
    {
        if x == 0 then 0 else 1
    }

    lemma lemma_ge_mod_correct(
        a: seq<uint32>,
        n: seq<uint32>,
        i: nat,
        result: uint32)

        requires |a| == |n|
        requires 0 <= i < |a|
        requires a[i+1..] == n[i+1..]
        requires result != 0 ==> a[i] < n[i]
        requires i != 0 ==> (result == 0 ==> a[i] > n[i])
        requires i == 0 ==> (result == 0 ==> a[i] >= n[i])

        ensures result != 0 ==> to_nat(a) < to_nat(n);
        ensures result == 0 ==> to_nat(a) >= to_nat(n);
    {
        cmp_sufficient_lemma(a, n, i);
        
        assert result != 0 ==> to_nat(a) < to_nat(n);
        if i != 0 {
            assert result == 0 ==> to_nat(a) >= to_nat(n);
        } else {
            if a[i] > n[i] {
                assert result == 0 ==> to_nat(a) >= to_nat(n);
            } else {
                assert result == 0 ==> a[i] == n[i];
                assert result == 0 ==> a == n;
                assert result == 0 ==> to_nat(a) >= to_nat(n);
            }
        }
    }

    predicate sub_mod_A_inv(lh: uint32, uh: uint32)
    {
        || (lh == uh == 0)
        || (lh == uh == 0xffff_ffff)
    }

    function A_as_carry(lh: uint32, uh: uint32): (c: uint1)
        requires sub_mod_A_inv(lh, uh)
    {
        if lh == 0 then 0 else 1
    }

    predicate sub_mod_loop_inv(
        old_a: seq<uint32>,
        n: seq<uint32>,
        a: seq<uint32>,
        i: nat,
        lh: uint32,
        uh: uint32)
    {
        && sub_mod_A_inv(lh, uh)
        && |old_a| == |a| == |n|
        && 0 <= i <= |a|
        && old_a[i..] == a[i..]
        && GBV.BVSEQ.SeqSub(old_a[..i], n[..i]) == (a[..i], A_as_carry(lh, uh))
    }

    lemma halves_equal_neg_one(lh: uint32, uh: uint32)
        requires lh == 0xffff_ffff
        requires uh == to_uint32(int32_rs(to_int32(lh), 31))
        ensures lh == uh
    {
        calc == {
            uh;
            to_uint32(int32_rs(to_int32(lh), 31));
            {
                assert to_int32(lh) == -1;
            }
            to_uint32(int32_rs(-1, 31));
            to_uint32(-1 / Power2.Pow2(31));
            {
                Power2.Lemma2To64();
                div_negative_one(Power2.Pow2(31));
            }
            to_uint32(-1);
            0xffff_ffff;
        }
    }

    lemma halves_equal_zero(lh: uint32, uh: uint32)
        requires lh == 0
        requires uh == to_uint32(int32_rs(to_int32(lh), 31))
        ensures uh == 0
    {
        assert uh == to_uint32(int32_rs(0, 31));
        assume int32_rs(0, 31) == 0;
    }

    lemma halves_equal(lh: uint32, uh: uint32)
        requires lh == 0xffff_ffff || lh == 0
        requires uh == to_uint32(int32_rs(to_int32(lh), 31))
        ensures uh == lh
    {
        if lh == 0xffff_ffff {
            halves_equal_neg_one(lh, uh);
        } else {
            halves_equal_zero(lh, uh);
        }
    }

    lemma lemma_sub_mod_correct(
        old_a: seq<uint32>, n: seq<uint32>, a: seq<uint32>,
        v0: uint32, v1: uint32,
        lh: uint32, uh: uint32,
        lh': uint32, uh': uint32,
        carry_add: int, carry_sub: int,
        x13: uint32,
        i: nat)

        requires sub_mod_loop_inv(old_a, n, a, i, lh, uh)
        requires i < |a|

        requires v0 == uint32_add(lh, old_a[i]);
        requires x13 == uint32_sub(v0, n[i]);

        requires carry_add == uint32_lt(v0, old_a[i]);
        requires carry_sub == uint32_lt(v0, x13);
        requires v1 == uint32_add(uh, carry_add);

        requires lh' == uint32_sub(v1, carry_sub);
        requires uh' == to_uint32(int32_rs(to_int32(lh'), 31));

        ensures sub_mod_loop_inv(old_a, n, a[i := x13], i + 1, lh', uh')
    {
        var a_i := old_a[i];
        var n_i := n[i];

        var (zs, old_carry) := GBV.BVSEQ.SeqSub(old_a[..i], n[..i]);
        assert A_as_carry(lh, uh) == old_carry;

        var (z, carry) := subb(a_i, n_i, old_carry);

        var (zs_next, next_carry) := GBV.BVSEQ.SeqSub(old_a[..i+1], n[..i+1]);

        calc {
            zs_next;
            {
                assert(old_a[..i+1][..i] == old_a[..i]);
                assert(n[..i+1][..i] == n[..i]);
                reveal GBV.BVSEQ.SeqSub();
            }
            zs + [x13];
            {
                assert zs == a[..i];
            }
            a[..i] + [x13];
            a[i := x13][..i+1];
        }

        assert carry == next_carry by {
            assert old_a[..i+1][..i] == old_a[..i];
            assert n[..i+1][..i] == n[..i];
            reveal GBV.BVSEQ.SeqSub();
        }

        if uh == 0 {
            assert v1 == 0 || v1 == 1;
        } else {
            assert v1 == 0 || v1 == 0xffff_ffff;
        }
        assert lh' == 0 || lh' == 0xffff_ffff;

        halves_equal(lh', uh');
        assert sub_mod_A_inv(lh', uh');
        
        assert A_as_carry(lh', uh') == carry;
    }

    lemma sub_mod_post_lemma(old_a: seq<uint32>, n: seq<uint32>, a: seq<uint32>, lh: uint32, uh: uint32)
        requires sub_mod_loop_inv(old_a, n, a, |a|, lh, uh);
        ensures to_nat(a) == to_nat(old_a) - to_nat(n) + A_as_carry(lh, uh) * Power.Pow(BASE_32, |old_a|)
        ensures to_nat(old_a) >= to_nat(n) ==> A_as_carry(lh, uh) == 0;
    {
        var i := |old_a|;
        assert old_a[..i] == old_a;
        assert n[..i] == n;
        assert a[..i] == a;
        var cout := A_as_carry(lh, uh);
        assert GBV.BVSEQ.SeqSub(old_a, n) == (a, cout);
        GBV.BVSEQ.LemmaSeqSub(old_a, n, a, cout);

        if to_nat(old_a) >= to_nat(n) {
            GBV.BVSEQ.LemmaSeqNatBound(old_a);
            GBV.BVSEQ.LemmaSeqNatBound(n);
            GBV.BVSEQ.LemmaSeqNatBound(a);
            assert cout == 0;
        }
    }
}