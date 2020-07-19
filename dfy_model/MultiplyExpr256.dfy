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
    const B7 : int;

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

    // function interp_wide(wr: wide_register) : int
    // {
    //     wr[0] as int + wr[1] as int * BASE + 
    // }

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

        var t1 :uint256 := p3 + p4 + p5 + p6 * B + p7 * B + p8 * B + uh(t0);
        c_23 := lh(t1);

        var p10 :uint128 := mul_limb(a[3], b[1]);
        var p11 :uint128 := mul_limb(a[2], b[2]);
        var p12 :uint128 := mul_limb(a[1], b[3]);

        var p13 :uint128 := mul_limb(a[3], b[2]);
        var p14 :uint128 := mul_limb(a[2], b[3]);

        var t2 :uint256 := p10 + p11 + p12 + p13 * B + p14 * B + uh(t1);
        d_01 := lh(t2);

        var p15 :uint128 := mul_limb(a[3], b[3]);

        assume p15 + uh(t2) < UINT128_MAX;
        d_23 := p15 + uh(t2);
    }
}