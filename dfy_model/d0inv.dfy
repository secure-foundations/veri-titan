include "NativeTypes.dfy"
include "Powers.dfy"

module d0inv {
    import opened NativeTypes
    import opened Powers

    method d0inv(w28: uint32)
        requires w28 % 2 == 1;
    {
        var w0: uint32 := 2;
        var w29 : uint32 := 1;
        var i := 1;
        
        assert (w29 * w28) % power(2, i) == 1 
            && w0 == power(2, i) by {
            reveal power();
        }

        while i < 32
            invariant 1 <= i <= 32;
            invariant (w29 * w28) % power(2, i) == 1;
            invariant i != 32 ==> w0 == power(2, i);
            decreases 32 - i;
        {
            var w1 :uint32 := (w28 * w29) % UINT32_MAX;

            ghost var p :int := w1;
            ghost var w29_old := w29;

            w1 := (w1 as bv32 & w0 as bv32) as uint32;
            w29 := (w29 as bv32 | w1 as bv32) as uint32;

            if w1 == 0 {
                or_zero_nop_lemma(w29_old, w1);
                // assert w29_old == w29;
                d0inv_bv_lemma_1(w28 * w29, w0, i);
            } else {
                assume w29 == w29_old + w0;
                assume w1 == w0;

                // assert p == (w28 * w29_old) % UINT32_MAX;
                // assert (p as bv32 & w0 as bv32) as uint32 == w0;
                d0inv_aux_lemma(p, w29, w29_old, w28, w0, i);
            }

            if i != 31 {
                power_2_bounded_lemma(i + 1);
            }

            w0 := if i != 31 then power(2, i + 1) else 0;
            i := i + 1;
            assert i != 32 ==> w0 == power(2, i);
        }

        assert (w29 * w28) % power(2, 32) == 1;
    }

    lemma or_zero_nop_lemma(x: uint32, z: uint32)
        requires z == 0;
        ensures (x as bv32 | z as bv32) as uint32 == x;
    {
        assert z as bv32 == 0 by {
            bv32_uint32_casting(z as bv32, z);
        }
        assert x as bv32 | z as bv32 == x as bv32;
        bv32_uint32_casting(x as bv32, x);
    }

    lemma d0inv_aux_lemma(p: int, w29: int, w29_old: int, w28: uint32, w0: uint32, i: nat)
        requires w29 == w29_old + w0;

        requires p == (w28 * w29_old) % UINT32_MAX;
        requires w0 == power(2, i);
        requires w28 % 2 == 1;
        requires w28 * w29_old % w0 == 1;
        requires (p as bv32 & w0 as bv32) as uint32 == w0;

        ensures (w29 * w28) % power(2, i + 1) == 1;
    {
        assert w29 * w28 == w28 * w29_old + w28 * w0 by {
            d0inv_nl_aux_lemma(w29, w29_old, w28, w0);
        }

        assert (w28 * w29_old + w28 * w0) % power(2, i + 1) == 1 by {
            assert p as bv32 & w0 as bv32 == w0 as bv32 by {
                bv32_uint32_casting(p as bv32 & w0 as bv32, w0);
            }
            d0inv_bv_lemma_2(w28 * w29_old, w28, w0, i);
        }

        assert (w29 * w28) % power(2, i + 1) == 1;
    }

    lemma d0inv_nl_aux_lemma(w29: int, w29_old: int, w28: uint32, w0: uint32)
        requires w29 == w29_old + w0;
        ensures w29 * w28 == w28 * w29_old + w28 * w0;
    {
        assert true;
    }

    lemma bv32_uint32_casting(bvx: bv32, uintx: uint32)
        ensures (bvx as uint32 == uintx) <==> (bvx == uintx as bv32);

    lemma power_2_bounded_lemma(i: int)
        requires 0 <= i < 32;
        ensures power(2, i) <= UINT32_MAX; 
    
    lemma {:axiom} d0inv_bv_lemma_1(x: int, w0: uint32, i: nat)
        requires w0 == power(2, i);
        requires x % w0 == 1;
        requires (x % UINT32_MAX) as bv32 & w0 as bv32 == 0;
        ensures x % power(2, i + 1) == 1;

    lemma {:axiom} d0inv_bv_lemma_2(x: int, w28: uint32, w0: uint32, i: nat)
        requires w0 == power(2, i);
        requires x % w0 == 1;
        requires ((x % UINT32_MAX) as bv32) & (w0 as bv32) == (w0 as bv32);
        requires w28 % 2 == 1;
        ensures (x + w28 * w0) % power(2, i + 1) == 1;
}