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
        ensures B() != 0;
    {
        UINT64_MAX as int + 1
    }

    function method lh(x: uint128) : (r: uint64)

 	function method uh(x: uint128) : (r: uint64)

 	lemma split_lemma(x: uint128)
 	 	ensures lh(x) as int * B() + lh(x) as int == x as int;
 	 	ensures lh(x) as int == x as int % B();

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
        
        var t1 : uint128 := uh(p1) as uint128 + lh(p2) as uint128 + lh(p3) as uint128;
        assume uh(t1) <= 1;
        var t2 : uint128 := uh(p2) as uint128 + uh(p3) as uint128 + lh(p4) as uint128 + uh(t1) as uint128;
        assume uh(p4) as int + uh(t2) as int <= UINT64_MAX as int;
        var t3 : uint64 := uh(p4) + uh(t2);

        c := c[0 := lh(p1)]; 
        c := c[1 := lh(t1)];
        c := c[2 := lh(t2)];
        c := c[3 := t3];

        calc == {
            c[0] as int + c[1] as int * B() + c[2] as int * B() * B() + c[3] as int * B() * B() * B();
            lh(p1) as int + lh(t1) as int * B() + lh(t2) as int * B() * B() + t3 as int * B() * B() * B();
            lh(p1) as int + lh(t1) as int * B() + lh(t2) as int * B() * B() + (uh(p4) + uh(t2)) as int * B() * B() * B();
            lh(p1) as int + lh(t1) as int * B() + lh(t2) as int * B() * B() + uh(p4) as int * B() * B() * B() + uh(t2) as int * B() * B() * B();
            {
                assume lh(t2) as int * B() * B() + uh(t2) as int * B() * B() * B() == t2 as int * B() * B();
            }
            lh(p1) as int + lh(t1) as int * B() + t2 as int * B() * B() + uh(p4) as int * B() * B() * B();
            {
                assert t2 as int == uh(p2) as int + uh(p3) as int + lh(p4) as int + uh(t1) as int;
            }
            lh(p1) as int + lh(t1) as int * B() + (uh(p2) as int + uh(p3) as int + lh(p4) as int + uh(t1) as int) * B() * B() + uh(p4) as int * B() * B() * B();
            lh(p1) as int + lh(t1) as int * B() + uh(p2) as int * B() * B() + uh(p3) as int * B() * B() + lh(p4) as int * B() * B() + uh(t1) as int * B() * B() + uh(p4) as int * B() * B() * B();
            {
                assume lh(p4) as int * B() * B() + uh(p4) as int * B() * B() * B() == p4 as int * B() * B(); 
            }
            lh(p1) as int + lh(t1) as int * B() + uh(p2) as int * B() * B() + uh(p3) as int * B() * B() + uh(t1) as int * B() * B() + p4 as int * B() * B();
            {
                assume lh(t1) as int * B() + uh(t1) as int * B() * B() == t1 * B(); 
            }
            lh(p1) as int + uh(p2) as int * B() * B() + uh(p3) as int * B() * B() + t1 as int * B() + p4 as int * B() * B();
            {
                assert t1 as int == uh(p1) as int + lh(p2) as int + lh(p3) as int;
            }
            lh(p1) as int + uh(p2) as int * B() * B() + uh(p3) as int * B() * B() + (uh(p1) as int + lh(p2) as int + lh(p3) as int) * B() + p4 as int * B() * B();
            lh(p1) as int + uh(p2) as int * B() * B() + uh(p3) as int * B() * B() + uh(p1) as int * B() + lh(p2) as int * B() + lh(p3) as int * B() + p4 as int * B() * B();
            {
                assume uh(p3) as int * B() * B() + lh(p3) as int * B() == p3 as int * B();
            }
            lh(p1) as int + uh(p2) as int * B() * B() + p3 as int * B() + uh(p1) as int * B() + lh(p2) as int * B() + p4 as int * B() * B();
            {
                assume uh(p2) as int * B() * B() + lh(p2) as int * B() == p2 as int * B();
            }
            lh(p1) as int + p2 as int * B() + p3 as int * B() + uh(p1) as int * B() + p4 as int * B() * B();
            {
                assume uh(p1) as int * B() + lh(p1) as int == p1 as int;
            }
            p1 as int + p2 as int * B() + p3 as int * B() + p4 as int * B() * B();
        }
    }

    method mul_limb(a: uint64, b: uint64)
        returns (c: uint128)
        ensures c as int == a as int * b as int;
    {
        c := a as uint128 * b as uint128;
    }
}