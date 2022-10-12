include "../../../spec/arch/otbn/machine.s.dfy"
include "../../../spec/arch/otbn/vale.i.dfy"
include "../../../spec/bvop/bv256_op.s.dfy"
include "../../generic_falcon_lemmas.dfy"

module bv256_falcon_lemmas refines generic_falcon_lemmas {
    import MWD = bv256_op_s

    lemma lemma_montymul_correct(x: uint256, y: uint256, prod: uint256, sum: uint256,
        shifted: uint256, diff1: uint256, flags: flags_t, diff2: uint256)
      requires 0 <= x * y <= 150994944 
      requires prod == (x * y) * (Q * (Q-2))
      requires sum == otbn_addc(prod, x*y, SFT_DFT, false).0;
      requires shifted == otbn_addc(0, sum, SFT(false, 2), false).0;
      requires diff1 == otbn_subb(shifted, Q, SFT_DFT, false).0;
      requires flags == otbn_subb(shifted, Q, SFT_DFT, false).1;
      requires diff2 == otbn_addc(diff1, if flags.get_single_flag(0) then Q else 0, SFT_DFT, false).0;
      ensures IsModEquivalent(diff2 * 4091, x * y, 12289);
    {
        assert prod <= 22799472962568192 by { LemmaMulUpperBound(x * y, 150994944, Q * (Q-2), 150994943); }
        assert sum == prod + x * y;
        assert 0 <= sum < BASE_256;
        calc {
            shifted;
            bv256_op_s.rs(sum, 16);
            (sum / Power2.Pow2(16)) % BASE_256;
            { Power2.Lemma2To64(); }
            (sum / BASE_16) % BASE_256;
            sum / BASE_16;
        }

        gbassert IsModEquivalent(sum, 0, BASE_16) by {
            assert Q == 12289;
            assert BASE_16 == 65536;
            assert prod == (x * y) * (Q * (Q-2));
            assert sum == prod + x * y;
        }

        gbassert IsModEquivalent(diff2 * 4091, x * y, Q) by {
            assert Q == 12289;
            assert BASE_16 == 65536;
            assert prod == (x * y) * (Q * (Q-2));
            assert sum == prod + x * y;
            assert IsModEquivalent(4091, BASE_16, Q);
            assert shifted * BASE_16 == sum; 
            assert IsModEquivalent(sum, 0, BASE_16);
            assert IsModEquivalent(diff2, shifted, Q);
        }
    }

    predicate elems_iter_inv(heap: heap_t, iter: b256_iter, address: int, index: int)
    {
        && b256_iter_inv(heap, iter)
        && (address >= 0 ==> address == iter.cur_ptr())
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && valid_elems(iter.buff)
    }

    predicate nelems_iter_inv(heap: heap_t, iter: b256_iter, address: int, index: int)
    {
        && b256_iter_inv(heap, iter)
        && (address >= 0 ==> address == iter.cur_ptr())
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && valid_nelems(iter.buff)
    }

    predicate heap_b32_ptr_valid(heap: heap_t, base_ptr: nat, count: nat)
    {
        forall i: nat | i < count ::
            heap_w32_ptr_valid(heap, base_ptr + i * 4)
    }

    lemma heap_b32_ptr_specialize_lemma(heap: heap_t, base_ptr: nat, count: nat, i: nat)
        requires i < count;
        requires heap_b32_ptr_valid(heap, base_ptr, count);
        ensures heap_w32_ptr_valid(heap, base_ptr + i * 4);
    {
    }
    
    function b32_seq(heap: heap_t, base_ptr: nat, count: nat): seq<uint32>
        requires heap_b32_ptr_valid(heap, base_ptr, count);
    {
        seq(count, i requires 0 <= i < count =>
            heap_w32_read(heap, base_ptr + i * 4))
    }

    lemma heap_b256_write_preserves_b32_ptr_lemma(
        state: va_state, state': va_state,
        base_ptr: nat, count: nat, b256_ptr: uint32)
        requires valid_state_opaque(state);
        requires valid_state_opaque(state');
        requires heap_b32_ptr_valid(state.mem.heap, base_ptr, count);
        requires heap_b256_ptr_valid(state.mem.heap, b256_ptr);
        requires heap_b256_ptr_valid(state'.mem.heap, b256_ptr);
        requires state'.mem.heap ==
            state.mem.heap[b256_ptr := state'.mem.heap[b256_ptr]];
        ensures heap_b32_ptr_valid(state'.mem.heap, base_ptr, count);
        ensures b32_seq(state.mem.heap, base_ptr, count)
            == b32_seq(state'.mem.heap, base_ptr, count);
    {
        assume false;
    }
    // {
    //     reveal valid_state_opaque();

    //     var imem := state.mem.as_imem(flat);

    //     var b256_base_ptr := iter.base_ptr;
    //     var new_b256 := heap'[b256_base_ptr];

    //     assert heap' == heap[b256_base_ptr := new_b256];

    //     forall i: nat | i < count
    //         ensures heap_w32_ptr_valid(heap', base_ptr + i * 4);
    //         ensures heap'[base_ptr + i * 4] == heap[base_ptr + i * 4];
    //     {
    //         imem.heap_b256_write_preserves_w32_inv(flat, flat', iter, value, base_ptr + i * 4);
    //     }
    // }

    lemma heap_b256_writes_preserves_b32_ptr_lemma(
        state: va_state, state': va_state,
        base_ptr: nat, count: nat, b256_ptr1: uint32, b256_ptr2: uint32)
        requires valid_state_opaque(state);
        requires valid_state_opaque(state');
        requires heap_b32_ptr_valid(state.mem.heap, base_ptr, count);
        requires heap_b256_ptr_valid(state.mem.heap, b256_ptr1);
        requires heap_b256_ptr_valid(state.mem.heap, b256_ptr2);
        requires heap_b256_ptr_valid(state'.mem.heap, b256_ptr1);
        requires heap_b256_ptr_valid(state'.mem.heap, b256_ptr2);
        requires state'.mem.heap ==
            state.mem.heap[b256_ptr1 := state'.mem.heap[b256_ptr1]]
                [b256_ptr2 := state'.mem.heap[b256_ptr2]];
        ensures heap_b32_ptr_valid(state'.mem.heap, base_ptr, count);
        ensures b32_seq(state.mem.heap, base_ptr, count)
            == b32_seq(state'.mem.heap, base_ptr, count);
    {
        assume false;
    }

    lemma accumlate_lemma(a: seq<mword>, i: nat)
        returns (p: nat)
        requires valid_nelems(a);
        requires i < 512;
        ensures p == otbn_qmul(a[i], 0, a[i], 0);
        ensures p <= 37748736;
        ensures p == as_nelem(a[i]) * as_nelem(a[i]);
    {
        // var ai := a[i];
        assume false;
    }

    // lemma bound_lemma()
    // {
    //     var product := otbn_mulqacc_safe(false, old(src1), qwsel1, old(src2), qwsel2, shift, 0);
    //     let result := otbn_mulqacc_so(product, old(dst), lower, old(get_fgroup(fgroups, fg)));


    // }

}
