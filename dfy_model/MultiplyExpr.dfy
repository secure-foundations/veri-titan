include "../dfy_model/NativeTypes.dfy"

module MultiplyExpr {
    import opened NativeTypes

    type wide_register = wr:seq<uint64> |
        |wr| == 4
    witness
        [1, 2, 3, 4]

    type half_register = hr:seq<uint64> |
        |hr| == 2
    witness
        [1, 2]

    function method {: opaque} B() : int
    {
        UINT64_MAX as int + 1
    }

    // function interp_wide(wr: wide_register) : int
    // {
    //     wr[0] as int + wr[1] as int * BASE + 
    // }

    function interp_half(hr: half_register) : int
    {
        hr[0] as int + hr[1] as int * B()
    }

    method test_half_mul_1(a : half_register, b : half_register)
        returns (product: int)
        ensures interp_half(a) * interp_half(b) == product;
    {
        product := a[0] as int * b[0] as int +
            a[1] as int * b[0] as int * B() +
            a[0] as int * b[1] as int * B() +
            a[1] as int * b[1] as int * B() * B();
    }

    lemma product_fits(a: uint64, b: uint64)
        ensures a as uint128 * b as uint128 < 0x100000000000000000000000000000000;
    {
        assert a as int < 0x10000000000000000;
        assert b as int < 0x10000000000000000;
        assume a as int * b as int < 0x10000000000000000 * 0x10000000000000000;
        assert 0x10000000000000000 * 0x10000000000000000 <= 0x100000000000000000000000000000000;
    }

    method mul_limb(a: uint64, b: uint64)
        returns (c: uint128)
        ensures c as int == a as int * b as int;
    {
        c := a as uint128 * b as uint128;
    }

    method test_half_mul_2(a : half_register, b : half_register)
        returns (c : half_register, d: half_register)
        // ensures interp_half(a) * interp_half(b) == 
            // interp_half(c) * B() * B() + interp_half(d);
    {
        var accu :uint128 := mul_limb(a[0], b[0]);
        ghost var p1 := accu as int;

    }

 	// lemma split_lemma(x: uint64)
 	//  	ensures uh64(x) as int * (UINT32_MAX as int + 1) + lh64(x) as int == x as int;
 	//  	ensures lh64(x) as int == x as int % (UINT32_MAX as int + 1);

    function method lh(x: uint128) : (r: uint64)

 	function method uh(x: uint128) : (r: uint64)
}