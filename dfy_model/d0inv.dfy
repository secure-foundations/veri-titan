include "NativeTypes.dfy"
include "Powers.dfy"

module d0inv {
    import opened NativeTypes
    import opened Powers

    method d0inv(w28: uint256)
        requires w28 % 2 == 1;
    {
        var w0: uint256 := 2;
        var w29 : uint256 := 1;
        var i := 1;
        
        assert (w29 * w28) % power(2, i) == 1 
            && w0 == power(2, i) by {
            reveal power();
        }


        while i < 256
            invariant 1 <= i <= 256;
            // invariant (w29 * w28) % power(2, i) == 1;
            invariant i != 256 ==> w0 == power(2, i);
            decreases 256 - i;
        {
            var w1 :uint256 := (w28 * w29) % UINT256_MAX;

            ghost var p := w1;
            ghost var w29_old := w29;

            w1 := (w1 as bv256 & w0 as bv256) as uint256;
            w29 := (w29 as bv256 | w1 as bv256) as uint256;

            // and_single_bit_lemma(p, w1, w0, i);

            if w1 == 0 {
                // assume w29 == w29_old;
                assert (p as bv256 & w0 as bv256) as uint256 == 0;

                // d0inv_aux_lemma_1(p, w29, w29_old, w28, w0, i);

                // assume (w29 * w28) % power(2, i + 1) == 1;

                // or_zero_nop_lemma(w29_old, w1);
                // d0inv_bv_lemma_1(w28 * w29, w0, i);
            } else {
                assume w29 == w29_old + w0;
                assume w1 == w0;

                // assert p == (w28 * w29_old) % uint256_MAX;
                // assert (p as bv256 & w0 as bv256) as uint256 == w0;
                // d0inv_aux_lemma_2(p, w29, w29_old, w28, w0, i);
            }

            if i != 255 {
                power_2_bounded_lemma(i + 1);
            }

            w0 := if i != 255 then power(2, i + 1) else 0;
            i := i + 1;
            assert i != 256 ==> w0 == power(2, i);
        }

        // assert (w29 * w28) % power(2, 256) == 1;
    }

    lemma d0inv_aux_lemma_1(p: int, w29: int, w29_old: int, w28: uint256, w0: uint256, i: nat)
        // requires w29 == w29_old;

        // requires p == (w28 * w29_old) % UINT256_MAX;
        // requires w0 == power(2, i);
        // requires w28 % 2 == 1;
        // requires w28 * w29_old % w0 == 1;
        // requires (p as bv256 & w0 as bv256) as uint256 == 0;

        ensures (w29 * w28) % power(2, i + 1) == 1;



    lemma {:axiom} and_single_bit_lemma(x: uint256, x': uint256, w0: uint256, i: nat)
        requires w0 == power(2, i);
        requires x' == (x as bv256 & w0 as bv256) as uint256;
        ensures x' == power(2, i) || x' == 0;

    lemma or_zero_nop_lemma(x: uint256, z: uint256)
        requires z == 0;
        ensures (x as bv256 | z as bv256) as uint256 == x;
    {
        assert z as bv256 == 0 by {
            bv256_uint256_casting(z as bv256, z);
        }
        assert x as bv256 | z as bv256 == x as bv256;
        bv256_uint256_casting(x as bv256, x);
    }

    lemma {:timeLimit 10} d0inv_aux_lemma_2(p: int, w29: int, w29_old: int, w28: uint256, w0: uint256, i: nat)
        requires w29 == w29_old + w0;

        requires p == (w28 * w29_old) % UINT256_MAX;
        requires w0 == power(2, i);
        requires w28 % 2 == 1;
        requires w28 * w29_old % w0 == 1;
        requires (p as bv256 & w0 as bv256) as uint256 == w0;

        ensures (w29 * w28) % power(2, i + 1) == 1;
    {
        assert w29 * w28 == w28 * w29_old + w28 * w0 by {
            d0inv_nl_aux_lemma(w29, w29_old, w28, w0);
        }

        assert (w28 * w29_old + w28 * w0) % power(2, i + 1) == 1 by {
            assert p as bv256 & w0 as bv256 == w0 as bv256 by {
                bv256_uint256_casting(p as bv256 & w0 as bv256, w0);
            }
            d0inv_bv_lemma_2(w28 * w29_old, w28, w0, i);
        }

        assert (w29 * w28) % power(2, i + 1) == 1;
    }

    lemma d0inv_nl_aux_lemma(w29: int, w29_old: int, w28: uint256, w0: uint256)
        requires w29 == w29_old + w0;
        ensures w29 * w28 == w28 * w29_old + w28 * w0;
    {
        assert true;
    }

    lemma {:axiom} bv256_uint256_casting(bvx: bv256, uintx: uint256)
        ensures (bvx as uint256 == uintx) <==> (bvx == uintx as bv256);

    lemma power_2_bounded_lemma(i: int)
        requires 0 <= i < 256;
        ensures power(2, i) <= UINT256_MAX; 
    
    lemma {:axiom} d0inv_bv_lemma_1(x: int, w0: uint256, i: nat)
        requires w0 == power(2, i);
        requires x % w0 == 1;
        requires (x % UINT256_MAX) as bv256 & w0 as bv256 == 0;
        ensures x % power(2, i + 1) == 1;

    lemma {:axiom} d0inv_bv_lemma_2(x: int, w28: uint256, w0: uint256, i: nat)
        requires w0 == power(2, i);
        requires x % w0 == 1;
        requires ((x % UINT256_MAX) as bv256) & (w0 as bv256) == (w0 as bv256);
        requires w28 % 2 == 1;
        ensures (x + w28 * w0) % power(2, i + 1) == 1;
}