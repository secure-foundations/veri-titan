include "NativeTypes.dfy"
include "Powers.dfy"

module d0inv {
    import opened NativeTypes
    import opened Powers

    method d0inv(w28: uint256)
        requires w28 % 2 == 1;
        requires w28 < UINT256_MAX;
    {
        var w0: uint256 := 1;
        var w29 : uint256 := 1;
        var i := 0;
        
        assert w0 == power(2, 0) by {
            reveal power();
        }

        while i < 256
            invariant 0 <= i <= 256;
            invariant (i == 0) ==> w29 == 1;
            invariant (i > 0) ==> ((w29 * w28) % power(2, i) == 1);
            invariant (i > 0) ==> (w29 < power(2, i));
            invariant (i < 256) ==> w0 == power(2, i);
            decreases 256 - i;
        {
            var w1 :uint256 := (w28 * w29) % UINT256_MAX;

            ghost var w1_old := w1;
            ghost var w29_old := w29;

            w1 := and_256(w1, w0);
            w29 := or_256(w29, w1);

            if i == 0 {
                assert w1_old == w28 * w29_old;
                odd_and_one_lemma(w1_old);
                assert w29 == or_256(1, 1);
                assert w29 == 1 by {
                    reveal or_256();
                }
            } else {
                and_single_bit_lemma(w1, w1_old, w0, i);

                if w1 == 0 {
                    or_zero_nop_lemma(w29_old, w1);
                    d0inv_bv_lemma_1(w28 * w29, w0, i);
                    assert w29 < power(2, i + 1) by {
                        reveal power();
                    }
                } else {
                    or_single_bit_add_lemma(w29, w29_old, w0, i);
                    d0inv_bv_lemma_2(w28 * w29_old, w28, w0, i);
                }
            }

            if i != 255 {
                power_2_bounded_lemma(i + 1);
            }

            w0 := if i != 255 then power(2, i + 1) else 0;
            i := i + 1;
            assert i != 256 ==> w0 == power(2, i);

            if i == 1 {
                assert w0 == 2 by {
                    reveal power();
                }
            }
        }

        assert (w29 * w28) % power(2, 256) == 1;
    }

    function method {:opaque} and_256(a:uint256, b:uint256) : uint256
    {
        (a as bv256 & b as bv256) as uint256
    }

    function method {:opaque} or_256(a:uint256, b:uint256) : uint256
    {
        (a as bv256 | b as bv256) as uint256
    }
    
    // lemma mod_max_nop_lemma(x: uint256)
    //     requires 
    //     ensures x % UINT256_MAX == x;
    // {
    //     assert x <= 
    // }

    lemma {:axiom} odd_and_one_lemma(x: uint256) 
        requires x % 2 == 1;
        ensures and_256(x, 1) == 1;

    lemma {:axiom} and_single_bit_lemma(x': uint256, x: uint256, w0: uint256, i: nat)
        requires w0 == power(2, i);
        requires x' == and_256(x, w0);
        ensures x' == power(2, i) || x' == 0;

    lemma {:axiom} or_zero_nop_lemma(x: uint256, z: uint256)
        requires z == 0;
        ensures or_256(x, z) == x;

    lemma {:axiom} or_single_bit_add_lemma(x': uint256, x: uint256, w0: uint256, i: nat)
        requires w0 == power(2, i);
        requires x < power(2, i);
        requires x' == or_256(x, w0);
        ensures x' == x + w0;
        ensures x' < power(2, i + 1);

    // lemma {:axiom} bv256_uint256_casting(bvx: bv256, uintx: uint256)
    //     ensures (bvx as uint256 == uintx) <==> (bvx == uintx as bv256);

    lemma power_2_bounded_lemma(i: int)
        requires 0 <= i < 256;
        ensures power(2, i) <= UINT256_MAX;

    lemma {:axiom} d0inv_bv_lemma_1(x: int, w0: uint256, i: nat)
        requires w0 == power(2, i);
        requires x % w0 == 1;
        requires and_256(x % UINT256_MAX, w0) == 0;
        ensures x % power(2, i + 1) == 1;

    lemma {:axiom} d0inv_bv_lemma_2(x: int, w28: uint256, w0: uint256, i: nat)
        requires w0 == power(2, i);
        requires x % w0 == 1;
        requires and_256(x % UINT256_MAX, w0) == w0;
        requires w28 % 2 == 1;
        ensures (x + w28 * w0) % power(2, i + 1) == 1;
}