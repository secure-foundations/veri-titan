include "NativeTypes.dfy"

module MultiplyExpr256 {
    import opened NativeTypes

    type wide_register = wr:seq<uint64> |
        |wr| == 4
    witness
        [1, 2, 3, 4]

    const B : int := UINT64_MAX as int + 1;
    const B2 : int := B * B;
    const B3 : int;
    const B4 : int;
    const B5 : int;
    const B6 : int;

    function method lh(x: uint256) : uint128
        ensures flh(x) == lh(x) as int;

    function flh(x: int) : (r: int)

 	function method uh(x: uint256) : (r: uint128)
        ensures fuh(x) == uh(x) as int;

    function fuh(x: int) : (r: int)

 	lemma split_lemma(x: uint256)
 	 	ensures flh(x) * B2 + flh(x) == x;
 	 	ensures flh(x) == x % B2;

    method mul_limb(a: uint64, b: uint64)
        returns (c: uint128)
        ensures c as int == a as int * b as int;
    {
        c := a as uint128 * b as uint128;
    }

    function interp_wide(wr: wide_register) : int
    {
        wr[0] + wr[1] * B + wr[2] * B2 + wr[3] * B3
    }

    method test_full_mul(a : wide_register, b : wide_register)
        returns (c_01: uint128, c_23: uint128, d_01: uint128, d_23: uint128)
    {
        var p0 :uint128 := mul_limb(a[0], b[0]);
        var p1 :uint128 := mul_limb(a[1], b[0]);
        var p2 :uint128 := mul_limb(a[0], b[1]);

        var t0 :uint256 := p0 + p1 * B + p2 * B;
        c_01 := lh(t0);

        var p3 :uint128 := mul_limb(a[2], b[0]);
        var p4 :uint128 := mul_limb(a[1], b[1]);
        var p5 :uint128 := mul_limb(a[0], b[2]);

        var p6 :uint128 := mul_limb(a[3], b[0]);
        var p7 :uint128 := mul_limb(a[2], b[1]);
        var p8 :uint128 := mul_limb(a[1], b[2]);
        var p9 :uint128 := mul_limb(a[0], b[3]);

        var t1 :uint256 := p3 + p4 + p5 + p6 * B + p7 * B + p8 * B + p9 * B + uh(t0);
        c_23 := lh(t1);

        var p10 :uint128 := mul_limb(a[3], b[1]);
        var p11 :uint128 := mul_limb(a[2], b[2]);
        var p12 :uint128 := mul_limb(a[1], b[3]);

        var p13 :uint128 := mul_limb(a[3], b[2]);
        var p14 :uint128 := mul_limb(a[2], b[3]);

        var t2 :uint256 := p10 + p11 + p12 + p13 * B + p14 * B + uh(t1);
        d_01 := lh(t2);

        var p15 :uint128 := mul_limb(a[3], b[3]);
        var t3 :uint256 := p15 + uh(t2);

        d_23 := lh(t3);

        assume d_23 == t3;
        test_full_mul_lemma(a, b, t0, t1, t2, t3, c_01, c_23, d_01, d_23);
    }

    lemma test_full_mul_lemma(
        a : wide_register, b : wide_register,
        t0 : uint256, t1 : uint256, t2 : uint256, t3 : uint256,
        c_01: uint128, c_23: uint128, d_01: uint128, d_23: uint128)
        
        requires t0 == a[0] * b[0] + 
            a[1] * b[0] * B + a[0] * b[1] * B;
        requires t1 == a[2] * b[0] + a[1] * b[1] + a[0] * b[2] +
            a[3] * b[0] * B + a[2] * b[1] * B + a[1] * b[2] * B + a[0] * b[3] * B + uh(t0);
        requires t2 == a[3] * b[1] + a[2] * b[2] + a[1] * b[3] + 
            a[3] * b[2] * B + a[2] * b[3] * B + uh(t1);
        requires t3 == a[3] * b[3] + uh(t2);

        requires c_01 == lh(t0);
        requires c_23 == lh(t1);
        requires d_01 == lh(t2);
        requires d_23 == t3;
    {
        var g0 := a[2] * b[0] + a[1] * b[1] + a[0] * b[2] +
            a[3] * b[0] * B + a[2] * b[1] * B + a[1] * b[2] * B + a[0] * b[3] * B;

        var g1 := a[3] * b[1] + a[2] * b[2] + a[1] * b[3] + 
            a[3] * b[2] * B + a[2] * b[3] * B;

        var g2 :int := a[3] as int * b[3];

        assert t1 == g0 + uh(t0);
        assert t2 == g1 + uh(t1);
        assert t3 == g2 + uh(t2);

        calc == {
            c_01 + c_23 * B2 + d_01 * B4 + d_23 * B6;
            c_01 + c_23 * B2 + d_01 * B4 + (g2 + uh(t2)) * B6;
            c_01 + c_23 * B2 + lh(t2) * B4 + (g2 + uh(t2)) * B6;
            c_01 + c_23 * B2 + lh(t2) * B4 + g2 * B6 + uh(t2) * B6;
            {
                assume lh(t2) * B4 + uh(t2) * B6 == t2 * B4;
            }
            c_01 + c_23 * B2 + t2 * B4 + g2 * B6;
            c_01 + lh(t1) * B2 + t2 * B4 + g2 * B6;
            c_01 + lh(t1) * B2 + (g1 + uh(t1)) * B4 + g2 * B6;
            c_01 + lh(t1) * B2 + g1 * B4 + uh(t1) * B4 + g2 * B6;
            {
                assume lh(t1) * B2 + uh(t1) * B4 == t1 * B2;
            }
            c_01 + t1 * B2 + g1 * B4 + g2 * B6;
            lh(t0) + t1 * B2 + g1 * B4 + g2 * B6;
            lh(t0) + (g0 + uh(t0)) * B2 + g1 * B4 + g2 * B6;
            lh(t0) + g0 * B2 + uh(t0) * B2 + g1 * B4 + g2 * B6;
            {
                assume lh(t0) + uh(t0) * B2 == t0;
            }
            t0 + g0 * B2 + g1 * B4 + g2 * B6;
        }
    }

    lemma test_full_mul_aux_lemma(a: wide_register, b: wide_register,
        t0: int, g0: int, g1: int, g2: int)

        requires t0 == a[0] * b[0] + 
            a[1] * b[0] * B + a[0] * b[1] * B;
        requires g0 == a[2] * b[0] + a[1] * b[1] + a[0] * b[2] +
            a[3] * b[0] * B + a[2] * b[1] * B + a[1] * b[2] * B + a[0] * b[3] * B;
        requires g1 == a[3] * b[1] + a[2] * b[2] + a[1] * b[3] + 
            a[3] * b[2] * B + a[2] * b[3] * B;
        requires g2 == a[3] as int * b[3];

        ensures interp_wide(a) * interp_wide(b) == t0 + g0 * B2 + g1 * B4 + g2 * B6;
    {
        calc == {
            interp_wide(a) * interp_wide(b);
            ==
            (a[0] + a[1] * B + a[2] * B2 + a[3] * B3) * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3);
            ==
            a[0] * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3) +
            a[1] * B * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3) +
            a[2] * B2 * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3) +
            a[3] * B3 * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3);
            ==
            a[0] * b[0] + a[0] * b[1] * B + a[0] * b[2] * B2 + a[0] * b[3] * B3 +
            a[1] * B * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3) +
            a[2] * B2 * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3) +
            a[3] * B3 * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3);
            {
                assume a[1] * B * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3) ==
                    a[1] * b[0] * B + a[1] * b[1] * B2 + a[1] * b[2] * B3 + a[1] * b[3] * B4;
            }
            a[0] * b[0] + a[0] * b[1] * B + a[0] * b[2] * B2 + a[0] * b[3] * B3 +
            a[1] * b[0] * B + a[1] * b[1] * B2 + a[1] * b[2] * B3 + a[1] * b[3] * B4 +
            a[2] * B2 * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3) +
            a[3] * B3 * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3);
            ==
            t0 + a[0] * b[2] * B2 + a[0] * b[3] * B3 +
            a[1] * b[1] * B2 + a[1] * b[2] * B3 + a[1] * b[3] * B4 +
            a[2] * B2 * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3) +
            a[3] * B3 * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3);
            {
                assume a[2] * B2 * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3) ==
                    a[2] * b[0] * B2 + a[2] * b[1] * B3 + a[2] * b[2] * B4 + a[2] *b[3] * B5;
            }
            t0 + a[0] * b[2] * B2 + a[0] * b[3] * B3 +
            a[1] * b[1] * B2 + a[1] * b[2] * B3 + a[1] * b[3] * B4 +
            a[2] * b[0] * B2 + a[2] * b[1] * B3 + a[2] * b[2] * B4 + a[2] *b[3] * B5 +
            a[3] * B3 * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3);
            {
                assume a[3] * B3 * (b[0] + b[1] * B + b[2] * B2 + b[3] * B3) == 
                    a[3] * b[0] * B3 + a[3] * b[1] * B4 + a[3] * b[2] * B5 + a[3] * b[3] * B6;
            }
            t0 + a[0] * b[2] * B2 + a[0] * b[3] * B3 +
            a[1] * b[1] * B2 + a[1] * b[2] * B3 + a[1] * b[3] * B4 +
            a[2] * b[0] * B2 + a[2] * b[1] * B3 + a[2] * b[2] * B4 + a[2] *b[3] * B5 +
            a[3] * b[0] * B3 + a[3] * b[1] * B4 + a[3] * b[2] * B5 + a[3] * b[3] * B6;
            {
                assume g0 * B2 == a[2] * b[0] * B2 + a[1] * b[1] * B2 + a[0] * b[2] * B2 +
                    a[3] * b[0] * B3 + a[2] * b[1] * B3 + a[1] * b[2] * B3 + a[0] * b[3] * B3;
            }
            t0 + g0 * B2 +
            a[1] * b[3] * B4 +
            a[2] * b[2] * B4 + a[2] *b[3] * B5 +
            a[3] * b[1] * B4 + a[3] * b[2] * B5 + a[3] * b[3] * B6;
            {
                assume g1 * B4 == a[3] * b[1] * B4 + a[2] * b[2] * B4 + a[1] * b[3] * B4 + 
                    a[3] * b[2] * B5 + a[2] * b[3] * B5;
            }
            t0 + g0 * B2 + g1 * B4 + a[3] * b[3] * B6;
            t0 + g0 * B2 + g1 * B4 + g2 * B6;
        }
    }

}