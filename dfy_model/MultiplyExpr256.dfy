include "NativeTypes.dfy"

module MultiplyExpr256 {
    import opened NativeTypes

    type wide_register = wr:seq<uint64> |
        |wr| == 4
    witness
        [1, 2, 3, 4]

    const B : int := UINT64_MAX as int + 1;
    const B2 : int := B * B;
    const B3 : int := B * B * B;
    const B4 : int := B * B * B * B;
    const B5 : int := B * B * B * B * B;
    const B6 : int := B * B * B * B * B * B;

    // lemma shift_test(x: uint32)
    // {
    //     var shifted :bv16 := ((x as bv32) >> 16) as bv16;
    //     assert 0 <= shifted as int < 65536;
    // }

    function method {:opaque} lh(x: uint256) : uint128
    {
        assume false;
        (x as bv256 & 0xffffffffffffffffffffffffffffffff) as uint128
    }

 	function method {:opaque} uh(x: uint256) : uint128
    {
        assume false;
        (x as bv256 >> 128) as uint128
    }

 	lemma split_lemma(x: uint256)
 	 	ensures uh(x) * B2 + lh(x) == x;
 	 	ensures lh(x) == x % B2;

    function method mul_limb(a: uint64, b: uint64) : (p: uint128)
        ensures p == a as int * b as int;
    {
        a as uint128 * b as uint128
    }

    function interp_wide(wr: wide_register) : int
    {
        wr[0] + wr[1] * B + wr[2] * B2 + wr[3] * B3
    }

    method test_full_mul(a : wide_register, b : wide_register)
        returns (c_01: uint128, c_23: uint128, d_01: uint128, d_23: uint128)
        ensures c_01 + c_23 * B2 + d_01 * B4 + d_23 * B6 ==
            interp_wide(a) * interp_wide(b);
    {
        var a0 :uint256 := mul_limb(a[0], b[0]);
        var a1 :uint256 := a0 + mul_limb(a[1], b[0]) * B;
        var a2 :uint256 := a1 + mul_limb(a[0], b[1]) * B;
        c_01 := lh(a2);

        var a3 :uint256 := uh(a2) + mul_limb(a[2], b[0]);
        var a4 :uint256 := a3 + mul_limb(a[1], b[1]);
        var a5 :uint256 := a4 + mul_limb(a[0], b[2]);

        var a6 :uint256 := a5 + mul_limb(a[3], b[0]) * B;
        var a7 :uint256 := a6 + mul_limb(a[2], b[1]) * B;
        var a8 :uint256 := a7 + mul_limb(a[1], b[2]) * B;
        var a9 :uint256 := a8 + mul_limb(a[0], b[3]) * B;
        c_23 := lh(a9);

        var a10 :uint256 := uh(a9) + mul_limb(a[3], b[1]);
        var a11 :uint256 := a10 + mul_limb(a[2], b[2]);
        var a12 :uint256 := a11 + mul_limb(a[1], b[3]);

        var a13 :uint256 := a12 + mul_limb(a[3], b[2]) * B;
        var a14 :uint256 := a13 + mul_limb(a[2], b[3]) * B;
        d_01 := lh(a14);

        var a15 :uint256 := uh(a14) + mul_limb(a[3], b[3]);
        d_23 := lh(a15);

        assume d_23 == a15;
        test_full_mul_lemma(a, b, a2, a9, a14, a15, c_01, c_23, d_01, d_23);
    }

    lemma test_full_mul_lemma(
        a : wide_register, b : wide_register,
        a2 : uint256, a9: uint256, a14: uint256, a15 : uint256,
        c_01: uint128, c_23: uint128, d_01: uint128, d_23: uint128)
        
        requires a2 == a[0] * b[0] + 
            a[1] * b[0] * B + a[0] * b[1] * B;
        requires a9== a[2] * b[0] + a[1] * b[1] + a[0] * b[2] +
            a[3] * b[0] * B + a[2] * b[1] * B + a[1] * b[2] * B + a[0] * b[3] * B + uh(a2);
        requires a14== a[3] * b[1] + a[2] * b[2] + a[1] * b[3] + 
            a[3] * b[2] * B + a[2] * b[3] * B + uh(a9);
        requires a15 == a[3] * b[3] + uh(a14);

        requires c_01 == lh(a2);
        requires c_23 == lh(a9);
        requires d_01 == lh(a14);
        requires d_23 == a15;

        ensures c_01 + c_23 * B2 + d_01 * B4 + d_23 * B6 ==
            interp_wide(a) * interp_wide(b);
    {
        var g0 := a[2] * b[0] + a[1] * b[1] + a[0] * b[2] +
            a[3] * b[0] * B + a[2] * b[1] * B + a[1] * b[2] * B + a[0] * b[3] * B;

        var g1 := a[3] * b[1] + a[2] * b[2] + a[1] * b[3] + 
            a[3] * b[2] * B + a[2] * b[3] * B;

        var g2 :int := a[3] as int * b[3];

        assert a9 == g0 + uh(a2);
        assert a14 == g1 + uh(a9);
        assert a15 == g2 + uh(a14);

        calc == {
            c_01 + c_23 * B2 + d_01 * B4 + d_23 * B6;
            c_01 + c_23 * B2 + d_01 * B4 + (g2 + uh(a14)) * B6;
            c_01 + c_23 * B2 + lh(a14) * B4 + (g2 + uh(a14)) * B6;
            c_01 + c_23 * B2 + lh(a14) * B4 + g2 * B6 + uh(a14) * B6;
            {
        		split_lemma(a14);
            }
            c_01 + c_23 * B2 + a14* B4 + g2 * B6;
            c_01 + lh(a9) * B2 + a14* B4 + g2 * B6;
            c_01 + lh(a9) * B2 + (g1 + uh(a9)) * B4 + g2 * B6;
            c_01 + lh(a9) * B2 + g1 * B4 + uh(a9) * B4 + g2 * B6;
            {
        		split_lemma(a9);
            }
            c_01 + a9* B2 + g1 * B4 + g2 * B6;
            lh(a2) + a9* B2 + g1 * B4 + g2 * B6;
            lh(a2) + (g0 + uh(a2)) * B2 + g1 * B4 + g2 * B6;
            lh(a2) + g0 * B2 + uh(a2) * B2 + g1 * B4 + g2 * B6;
            {
        		split_lemma(a2);
            }
            a2 + g0 * B2 + g1 * B4 + g2 * B6;
            {
                test_full_mul_aux_lemma(a, b, a2, g0, g1, g2);
            }
            interp_wide(a) * interp_wide(b);
        }
    }

    lemma test_full_mul_aux_lemma(a: wide_register, b: wide_register,
        a2: int, g0: int, g1: int, g2: int)

        requires a2 == a[0] * b[0] + 
            a[1] * b[0] * B + a[0] * b[1] * B;
        requires g0 == a[2] * b[0] + a[1] * b[1] + a[0] * b[2] +
            a[3] * b[0] * B + a[2] * b[1] * B + a[1] * b[2] * B + a[0] * b[3] * B;
        requires g1 == a[3] * b[1] + a[2] * b[2] + a[1] * b[3] + 
            a[3] * b[2] * B + a[2] * b[3] * B;
        requires g2 == a[3] as int * b[3];

        ensures interp_wide(a) * interp_wide(b) == a2 + g0 * B2 + g1 * B4 + g2 * B6;
    {
        assert true;
    }
}