include "../../../spec/arch/otbn/machine.s.dfy"
include "../../../spec/arch/otbn/vale.i.dfy"
include "../../../spec/bvop/bv256_op.s.dfy"
include "../../generic_falcon_lemmas.dfy"

module bv256_falcon_lemmas refines generic_falcon_lemmas {
    import MWD = bv256_op_s

    import opened ot_vale
    import opened ot_machine
    import opened mem
    import flat

    lemma addm_correct_lemma(x: uint256, y:uint256, mod: uint256)
        requires x < mod;
        requires y < mod;
        ensures 0 <= otbn_addm(x, y, mod) < mod;
        ensures otbn_addm(x, y, mod) == (x + y) % mod;
    {
        assert (x + y) < 2 * mod;

        if (x + y) < mod {
            assert (x + y) % mod == otbn_addm(x, y, mod) by { DivMod.LemmaSmallMod((x + y), mod); }
        } else { 
            assert mod <= x + y < 2 * mod;
            calc == {
                otbn_addm(x, y, mod);
                (x + y - mod) % BASE_256;
                { assert x + y - mod < BASE_256; }
                (x + y - mod);
                {
                    assert 0 <= x + y - mod < mod;
                    DivMod.LemmaSmallMod(x + y - mod, mod);
                }
                (x + y - mod) % mod;
                { DivMod.LemmaModSubMultiplesVanishAuto(); }
                (x + y) % mod;
            }
        }
    }

    lemma subm_correct_lemma(x: uint256, y: uint256, mod: uint256)
        requires x < mod;
        requires y < mod;
        ensures 0 <= otbn_subm(x, y, mod) < mod;
        ensures otbn_subm(x, y, mod) == (x - y) % mod;
    {
        var diff : int := x as int - y as int;
        assert -(mod as int) < diff < mod;

        if diff >= 0 {
            assert diff < mod;
            assert diff % mod == otbn_subm(x, y, mod) by { DivMod.LemmaSmallMod(diff, mod); }
        } else {
            calc == {
                otbn_subm(x, y, mod);
                (diff + mod) % BASE_256;
                { assert 0 <= diff + mod < BASE_256; }
                (diff + mod);
                {
                    assert 0 <= diff + mod < mod;
                    DivMod.LemmaSmallMod(diff + mod, mod);
                }
                (diff + mod) % mod;
                { DivMod.LemmaModAddMultiplesVanish(diff, mod); }
                diff % mod;
            }
        }
    }

    lemma lemma_elem_prod_bound(x: uint256, y: uint256, r: uint256)
        requires x < 12289 && y < 12289
        requires r == x * y
        ensures r <= 150994944
    {
        LemmaMulUpperBound(x, 12288, y, 12288);
    }

    lemma lemma_small(x:uint256)
      requires x < BASE_64
      ensures bv256_op_s.lh(x) % BASE_64 == x
    {
        calc{
            bv256_op_s.lh(x) % BASE_64;
            { reveal bv256_op_s.lh(); }
            (x % BASE_256) % BASE_64;
            { LemmaSmallMod(x, BASE_256); }
            x % BASE_64;
            { LemmaSmallMod(x, BASE_64); }
            x;
        }
    }

    lemma lemma_small_mulqacc(x: uint256, y: uint256, r: uint256, old_wacc: uint256, old_flags: flags_t)
      requires x < BASE_64 && y < BASE_64
      requires var product := otbn_mulqacc(true, x, 0, y, 0, 0, old_wacc);
               r == otbn_mulqacc_so(product, 0, true, old_flags).new_dst
      ensures r == x * y
    {
        LemmaMulUpperBound(x, BASE_64 - 1, y, BASE_64 - 1);
        var product := otbn_mulqacc(true, x, 0, y, 0, 0, old_wacc);
        calc {
            product;
            otbn_shift(otbn_qmul(x, 0, y, 0), SFT(true, 0 * 8));
            otbn_shift(otbn_qmul(x, 0, y, 0), SFT(true, 0));
            otbn_qmul(x, 0, y, 0);
            { reveal otbn_qmul(); }
            otbn_qsel(x, 0) as uint128 * otbn_qsel(y, 0) as uint128;
            { reveal otbn_qsel(); }
            ((bv256_op_s.lh(x) % BASE_64) as uint128) * ((bv256_op_s.lh(y) % BASE_64) as uint128);
            { lemma_small(x); lemma_small(y); }
            x as uint128 * y as uint128;
            x * y;
        }
      
        calc {
            bv256_op_s.lh(product);
            { reveal bv256_op_s.lh(); LemmaSmallMod(x, BASE_256); }
            x * y;
        }
      
        calc {
            otbn_hwb(0, x * y, true);
            { reveal otbn_hwb(); }
            x * y + bv256_op_s.uh(0) * BASE_128;
            { reveal bv256_op_s.uh(); }
            x * y;
        }
    }

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
