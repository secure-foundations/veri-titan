include "../arch/msp430/machine.s.dfy"
include "generic_mm_lemmas.dfy"
include "bv16_ops.dfy"
include "../arch/msp430/vale.i.dfy"

module bv16_mm_lemmas refines generic_mm_lemmas {
    import opened GBV = bv16_ops
    import opened msp_machine
    // import opened sub_mod_nl_lemmas
    import opened mem
    import opened msp_vale

    const NA : int := -1;

    const NUM_WORDS := 192;

    type uint32_view_t = dw_view_t

    predicate valid_uint32_view(
        num: uint32_view_t,
        lh: uint16, uh: uint16)
    {
        && lh == num.lh
        && uh == num.uh
    }

    predicate mvar_iter_inv(heap: heap_t, iter: iter_t, address: int, index: int, value: int)
    {
        && (address >= 0 ==> iter_inv(iter, heap, address))
        && (value >= 0 ==> to_nat(iter.buff) == value)
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == NUM_WORDS
    }

    // lemma mul16_correct_lemma(a: uint16, b: uint16, c: uint16, d: uint16)
    //     requires c == uint16_mul(a, b);
    //     requires d == uint16_mulhu(a, b);
    //     ensures to_nat([c, d]) == a * b;
    // {
    //     reveal dw_lh();
    //     reveal dw_uh();

    //     var full := a * b;
    //     dw_split_lemma(full);

    //     GBV.BVSEQ.LemmaSeqLen2([c, d]);
    // }

    // datatype mma_vars = mma_vars(
    //     iter_a: iter_t,
    //     a_i: uint16,
    //     i: nat,
    //     // d0: uint16,
    //     iter_b: iter_t,
    //     iter_c: iter_t, // writable
    //     iter_n: iter_t
    // )



    // predicate mma_vars_inv(
    //     vars: mma_vars,
    //     heap: heap_t,
    //     n_ptr: int, n_idx: int,
    //     c_ptr: int, c_idx: int,
    //     b_ptr: int, b_idx: int,
    //     rsa: rsa_params)
    // {
    //     && mvar_iter_inv(heap, vars.iter_a, -1, vars.i, NA)
    //     && vars.i <= NUM_WORDS
    //     && (vars.i < NUM_WORDS ==> vars.iter_a.buff[vars.i] == vars.a_i)
    //     && mvar_iter_inv(heap, vars.iter_n, n_ptr, n_idx, rsa.M)
    //     && mvar_iter_inv(heap, vars.iter_c, c_ptr, c_idx, NA)
    //     && mvar_iter_inv(heap, vars.iter_b, b_ptr, b_idx, NA)

    //     && vars.iter_c.base_ptr != vars.iter_a.base_ptr
    //     && vars.iter_c.base_ptr != vars.iter_n.base_ptr
    //     && vars.iter_c.base_ptr != vars.iter_b.base_ptr

    //     && rsa_params_inv(rsa)
    // }

    // datatype mm_vars = mm_vars_cons(
    //     iter_a: iter_t,
    //     iter_b: iter_t,
    //     iter_c: iter_t, // writable
    //     iter_n: iter_t
    // )

    // predicate mm_vars_inv(
    //     vars: mm_vars,
    //     heap: heap_t,
    //     a_ptr: int, a_idx: nat,
    //     n_ptr: int, n_idx: int,
    //     c_ptr: int, c_idx: int,
    //     b_ptr: int, b_idx: int,
    //     rsa: rsa_params)
    // {
    //     && mvar_iter_inv(heap, vars.iter_a, a_ptr, a_idx, NA)
    //     && mvar_iter_inv(heap, vars.iter_c, c_ptr, c_idx, NA)
    //     && mvar_iter_inv(heap, vars.iter_b, b_ptr, b_idx, NA)
    //     && mvar_iter_inv(heap, vars.iter_n, n_ptr, n_idx, rsa.M)

    //     && vars.iter_c.base_ptr != vars.iter_a.base_ptr
    //     && vars.iter_c.base_ptr != vars.iter_n.base_ptr
    //     && vars.iter_c.base_ptr != vars.iter_b.base_ptr

    //     && rsa_params_inv(rsa)
    // }

    // function to_mma_vars(vars: mm_vars, a_i: uint16): mma_vars
    // {
    //     mma_vars(vars.iter_a, a_i, vars.iter_a.index,
    //         vars.iter_b, vars.iter_c, vars.iter_n)
    // }

    function seq_zero(i: nat): seq<uint16>
    {
        GBV.BVSEQ.SeqZero(i)
    }

    // datatype mp_vars = mp_vars(
    //     iter_rr: iter_t, 
    //     iter_n: iter_t,
    //     iter_in: iter_t,
    //     iter_ar: iter_t, // writable
    //     iter_aar: iter_t, // writable
    //     iter_out: iter_t // writable
    // )

    // predicate mp_vars_inv(
    //     vars: mp_vars,
    //     heap: heap_t,
    //     rr_ptr: int,
    //     n_ptr: nat,
    //     in_ptr: nat,
    //     ar_ptr: nat,
    //     aar_ptr: nat,
    //     out_ptr: nat,
    //     rsa: rsa_params)
    // {
    //     && mvar_iter_inv(heap, vars.iter_rr, rr_ptr, 0, rsa.RR)
    //     && mvar_iter_inv(heap, vars.iter_n, n_ptr, 0, rsa.M)
    //     && mvar_iter_inv(heap, vars.iter_in, in_ptr, 0, rsa.SIG)
    //     && mvar_iter_inv(heap, vars.iter_ar, ar_ptr, 0, NA)
    //     && mvar_iter_inv(heap, vars.iter_aar, aar_ptr, 0, NA)
    //     && mvar_iter_inv(heap, vars.iter_out, out_ptr, 0, NA)

    //     && vars.iter_ar.base_ptr != vars.iter_rr.base_ptr
    //     && vars.iter_ar.base_ptr != vars.iter_n.base_ptr
    //     && vars.iter_ar.base_ptr != vars.iter_in.base_ptr
    //     && vars.iter_ar.base_ptr != vars.iter_aar.base_ptr
    //     && vars.iter_ar.base_ptr != vars.iter_out.base_ptr

    //     && vars.iter_aar.base_ptr != vars.iter_rr.base_ptr
    //     && vars.iter_aar.base_ptr != vars.iter_n.base_ptr
    //     && vars.iter_aar.base_ptr != vars.iter_in.base_ptr
    //     && vars.iter_aar.base_ptr != vars.iter_out.base_ptr

    //     && vars.iter_out.base_ptr != vars.iter_rr.base_ptr
    //     && vars.iter_out.base_ptr != vars.iter_n.base_ptr
    //     && vars.iter_out.base_ptr != vars.iter_in.base_ptr

    //     && rsa_params_inv(rsa)
    // }

    // lemma {:induction A, i} cmp_sufficient_lemma(A: seq<uint16>, B: seq<uint16>, i: nat)
    //     requires 0 <= i < |A| == |B|;
    //     requires forall j :: i < j < |A| ==> (A[j] == B[j]);
    //     ensures A[i] > B[i] ==> (to_nat(A) > to_nat(B));
    //     ensures A[i] < B[i] ==> (to_nat(A) < to_nat(B));
    // {
    //     var n := |A|;
    //     if n != 0 {
    //         if i == n - 1 {
    //             if A[n-1] > B[n-1] {
    //                 GBV.BVSEQ.LemmaSeqMswInequality(B, A);
    //             } else if A[n-1] < B[n-1] {
    //                 GBV.BVSEQ.LemmaSeqMswInequality(A, B);
    //             }
    //         } else {
    //             var n := |A|;
    //             var A' := A[..n-1];
    //             var B' := B[..n-1];

    //             calc ==> {
    //                 A[i] > B[i];
    //                 {
    //                     cmp_sufficient_lemma(A', B', i);
    //                 }
    //                 to_nat(A') > to_nat(B');
    //                 {
    //                     GBV.BVSEQ.LemmaSeqPrefix(A, n-1);
    //                     GBV.BVSEQ.LemmaSeqPrefix(B, n-1);
    //                 }
    //                 to_nat(A[..n-1]) > to_nat(B[..n-1]);
    //                 {
    //                   assert A[n-1] * Pow(BASE(), n-1) == B[n-1] * Pow(BASE(), n-1);
    //                 }
    //                 to_nat(A[..n-1]) + A[n-1] * Pow(BASE(), n-1) > to_nat(B[..n-1]) + B[n-1] * Pow(BASE(), n-1);
    //                 {
    //                   assert A[..n-1] + [A[n-1]] == A;
    //                   assert B[..n-1] + [B[n-1]] == B;
    //                 }
    //                 to_nat(A[..n-1]) + to_nat(A[n-1..]) * Pow(BASE(), n-1) > to_nat(B[..n-1]) + to_nat(B[n-1..]) * Pow(BASE(), n-1);
    //                 {
    //                     GBV.BVSEQ.LemmaSeqPrefix(A, n-1);
    //                     GBV.BVSEQ.LemmaSeqPrefix(B, n-1);
    //                     assert to_nat(A[..n-1]) + to_nat(A[n-1..]) * Pow(BASE(), n-1) == to_nat(A);
    //                     assert to_nat(B[..n-1]) + to_nat(B[n-1..]) * Pow(BASE(), n-1) == to_nat(B);
    //                 }
    //                 to_nat(A) > to_nat(B);
    //             }
    //             assert A[n-1] > B[n-1] ==> (to_nat(A) > to_nat(B));

    //             calc ==> {
    //                 A[i] < B[i];
    //                 {
    //                   cmp_sufficient_lemma(A', B', i);
    //                 }
    //                 to_nat(A') < to_nat(B');
    //                 {
    //                     GBV.BVSEQ.LemmaSeqPrefix(A, n-1);
    //                     GBV.BVSEQ.LemmaSeqPrefix(B, n-1);
    //                 }
    //                 to_nat(A[..n-1]) < to_nat(B[..n-1]);
    //                 {
    //                   assert A[n-1] * Pow(BASE(), n-1) == B[n-1] * Pow(BASE(), n-1);
    //                 }
    //                 to_nat(A[..n-1]) + A[n-1] * Pow(BASE(), n-1) < to_nat(B[..n-1]) + B[n-1] * Pow(BASE(), n-1);
    //                 {
    //                   assert A[..n-1] + [A[n-1]] == A;
    //                   assert B[..n-1] + [B[n-1]] == B;
    //                 }
    //                 to_nat(A[..n-1]) + to_nat(A[n-1..]) * Pow(BASE(), n-1) < to_nat(B[..n-1]) + to_nat(B[n-1..]) * Pow(BASE(), n-1);
    //                 {
    //                     GBV.BVSEQ.LemmaSeqPrefix(A, n-1);
    //                     GBV.BVSEQ.LemmaSeqPrefix(B, n-1);
    //                     assert to_nat(A[..n-1]) + to_nat(A[n-1..]) * Pow(BASE(), n-1) == to_nat(A);
    //                     assert to_nat(B[..n-1]) + to_nat(B[n-1..]) * Pow(BASE(), n-1) == to_nat(B);
    //                 }
    //                 to_nat(A) < to_nat(B);
    //             }
    //             assert A[n-1] < B[n-1] ==> (to_nat(A) < to_nat(B));
    //         }
    //     }
    // }

    // function uint16_to_bool(x: uint16) : bool
    // {
    //     if x == 0 then false else true
    // }

    // function uint16_to_uint1(x: uint16) : uint1
    // {
    //     if x == 0 then 0 else 1
    // }

    // lemma lemma_ge_mod_correct(
    //     a: seq<uint16>,
    //     n: seq<uint16>,
    //     i: nat,
    //     result: uint16)

    //     requires |a| == |n|
    //     requires 0 <= i < |a|
    //     requires a[i+1..] == n[i+1..]
    //     requires result != 0 ==> a[i] < n[i]
    //     requires i != 0 ==> (result == 0 ==> a[i] > n[i])
    //     requires i == 0 ==> (result == 0 ==> a[i] >= n[i])

    //     ensures result != 0 ==> to_nat(a) < to_nat(n);
    //     ensures result == 0 ==> to_nat(a) >= to_nat(n);
    // {
    //     cmp_sufficient_lemma(a, n, i);
        
    //     assert result != 0 ==> to_nat(a) < to_nat(n);
    //     if i != 0 {
    //         assert result == 0 ==> to_nat(a) >= to_nat(n);
    //     } else {
    //         if a[i] > n[i] {
    //             assert result == 0 ==> to_nat(a) >= to_nat(n);
    //         } else {
    //             assert result == 0 ==> a[i] == n[i];
    //             assert result == 0 ==> a == n;
    //             assert result == 0 ==> to_nat(a) >= to_nat(n);
    //         }
    //     }
    // }

    // predicate sub_mod_A_inv(lh: uint16, uh: uint16)
    // {
    //     || (lh == uh == 0)
    //     || (lh == uh == 0xffff_ffff)
    // }

    // function A_as_carry(lh: uint16, uh: uint16): (c: uint1)
    //     requires sub_mod_A_inv(lh, uh)
    // {
    //     if lh == 0 then 0 else 1
    // }

    // predicate sub_mod_loop_inv(
    //     old_a: seq<uint16>,
    //     n: seq<uint16>,
    //     a: seq<uint16>,
    //     i: nat,
    //     lh: uint16,
    //     uh: uint16)
    // {
    //     && sub_mod_A_inv(lh, uh)
    //     && |old_a| == |a| == |n|
    //     && 0 <= i <= |a|
    //     && old_a[i..] == a[i..]
    //     && GBV.BVSEQ.SeqSub(old_a[..i], n[..i]) == (a[..i], A_as_carry(lh, uh))
    // }

    // lemma halves_equal_neg_one(lh: uint16, uh: uint16)
    //     requires lh == 0xffff_ffff
    //     requires uh == to_uint16(int16_rs(to_int16(lh), 31))
    //     ensures lh == uh
    // {
    //     calc == {
    //         uh;
    //         to_uint16(int16_rs(to_int16(lh), 31));
    //         {
    //             assert to_int16(lh) == -1;
    //         }
    //         to_uint16(int16_rs(-1, 31));
    //         to_uint16(-1 / Power2.Pow2(31));
    //         {
    //             Power2.Lemma2To64();
    //             div_negative_one(Power2.Pow2(31));
    //         }
    //         to_uint16(-1);
    //         0xffff_ffff;
    //     }
    // }

    // lemma halves_equal_zero(lh: uint16, uh: uint16)
    //     requires lh == 0
    //     requires uh == to_uint16(int16_rs(to_int16(lh), 31))
    //     ensures uh == 0
    // {
    //     assert uh == to_uint16(int16_rs(0, 31));
    //     assume int16_rs(0, 31) == 0;
    // }

    // lemma halves_equal(lh: uint16, uh: uint16)
    //     requires lh == 0xffff_ffff || lh == 0
    //     requires uh == to_uint16(int16_rs(to_int16(lh), 31))
    //     ensures uh == lh
    // {
    //     if lh == 0xffff_ffff {
    //         halves_equal_neg_one(lh, uh);
    //     } else {
    //         halves_equal_zero(lh, uh);
    //     }
    // }

    // lemma lemma_sub_mod_correct(
    //     old_a: seq<uint16>, n: seq<uint16>, a: seq<uint16>,
    //     v0: uint16, v1: uint16,
    //     lh: uint16, uh: uint16,
    //     lh': uint16, uh': uint16,
    //     carry_add: int, carry_sub: int,
    //     x13: uint16,
    //     i: nat)

    //     requires sub_mod_loop_inv(old_a, n, a, i, lh, uh)
    //     requires i < |a|

    //     requires v0 == uint16_add(lh, old_a[i]);
    //     requires x13 == uint16_sub(v0, n[i]);

    //     requires carry_add == uint16_lt(v0, old_a[i]);
    //     requires carry_sub == uint16_lt(v0, x13);
    //     requires v1 == uint16_add(uh, carry_add);

    //     requires lh' == uint16_sub(v1, carry_sub);
    //     requires uh' == to_uint16(int16_rs(to_int16(lh'), 31));

    //     ensures sub_mod_loop_inv(old_a, n, a[i := x13], i + 1, lh', uh')
    // {
    //     var a_i := old_a[i];
    //     var n_i := n[i];

    //     var (zs, old_carry) := GBV.BVSEQ.SeqSub(old_a[..i], n[..i]);
    //     assert A_as_carry(lh, uh) == old_carry;

    //     var (z, carry) := subb(a_i, n_i, old_carry);

    //     var (zs_next, next_carry) := GBV.BVSEQ.SeqSub(old_a[..i+1], n[..i+1]);

    //     calc {
    //         zs_next;
    //         {
    //             assert(old_a[..i+1][..i] == old_a[..i]);
    //             assert(n[..i+1][..i] == n[..i]);
    //             reveal GBV.BVSEQ.SeqSub();
    //         }
    //         zs + [x13];
    //         {
    //             assert zs == a[..i];
    //         }
    //         a[..i] + [x13];
    //         a[i := x13][..i+1];
    //     }

    //     assert carry == next_carry by {
    //         assert old_a[..i+1][..i] == old_a[..i];
    //         assert n[..i+1][..i] == n[..i];
    //         reveal GBV.BVSEQ.SeqSub();
    //     }

    //     if uh == 0 {
    //         assert v1 == 0 || v1 == 1;
    //     } else {
    //         assert v1 == 0 || v1 == 0xffff_ffff;
    //     }
    //     assert lh' == 0 || lh' == 0xffff_ffff;

    //     halves_equal(lh', uh');
    //     assert sub_mod_A_inv(lh', uh');
        
    //     assert A_as_carry(lh', uh') == carry;
    // }

    // lemma sub_mod_post_lemma(old_a: seq<uint16>, n: seq<uint16>, a: seq<uint16>, lh: uint16, uh: uint16)
    //     requires sub_mod_loop_inv(old_a, n, a, |a|, lh, uh);
    //     ensures to_nat(a) == to_nat(old_a) - to_nat(n) + A_as_carry(lh, uh) * Power.Pow(BASE_16, |old_a|)
    //     ensures to_nat(old_a) >= to_nat(n) ==> A_as_carry(lh, uh) == 0;
    // {
    //     var i := |old_a|;
    //     assert old_a[..i] == old_a;
    //     assert n[..i] == n;
    //     assert a[..i] == a;
    //     var cout := A_as_carry(lh, uh);
    //     assert GBV.BVSEQ.SeqSub(old_a, n) == (a, cout);
    //     GBV.BVSEQ.LemmaSeqSub(old_a, n, a, cout);

    //     if to_nat(old_a) >= to_nat(n) {
    //         GBV.BVSEQ.LemmaSeqNatBound(old_a);
    //         GBV.BVSEQ.LemmaSeqNatBound(n);
    //         GBV.BVSEQ.LemmaSeqNatBound(a);
    //         assert cout == 0;
    //     }
    // }
}