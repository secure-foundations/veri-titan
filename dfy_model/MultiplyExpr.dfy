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

    method test_half_mul_2(a : half_register, b : half_register)
        returns (c : wide_register)
        // ensures interp_half(a) * interp_half(b) == 
            // interp_half(c) * B() * B() + interp_half(d);
    {
        var p1 :uint128 := mul_limb(a[0], b[0]);
        var p2 :uint128 := mul_limb(a[1], b[0]);
        var p3 :uint128 := mul_limb(a[0], b[1]);
        var p4 :uint128 := mul_limb(a[1], b[1]);
        
        assume uh(p1) <= 1;
        var t1 : uint128 := uh(p1) as uint128 + lh(p2) as uint128 + lh(p3) as uint128;
        assume uh(t1) <= 1;
        var t2 : uint128 := uh(p2) as uint128 + uh(p3) as uint128 + lh(p4) as uint128 + uh(t1) as uint128;
        assume uh(p4) as int + uh(t2) as int <= UINT64_MAX as int;
        var t3 : uint64 := uh(p4) + uh(t2);

        c := c[0 := lh(p1)]; 
        c := c[1 := lh(t1)];
        c := c[2 := lh(t2)];
        c := c[3 := t3];
    }

    method mul_limb(a: uint64, b: uint64)
        returns (c: uint128)
        ensures c as int == a as int * b as int;
    {
        c := a as uint128 * b as uint128;
    }

 	// lemma split_lemma(x: uint64)
 	//  	ensures uh64(x) as int * (UINT32_MAX as int + 1) + lh64(x) as int == x as int;
 	//  	ensures lh64(x) as int == x as int % (UINT32_MAX as int + 1);

    function method lh(x: uint128) : (r: uint64)

 	function method uh(x: uint128) : (r: uint64)
}