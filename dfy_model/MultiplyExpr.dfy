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

    function method B() : int
    {
        UINT64_MAX as int + 1
    }

    function method B2() : int
    function method B3() : int
    function method B4() : int
    function method B5() : int
    function method B6() : int
    function method B7() : int

    function method lh(x: uint128) : uint64
        ensures flh(x) == lh(x) as int;

    function flh(x: int) : (r: int)

 	function method uh(x: uint128) : (r: uint64)
        ensures fuh(x) == uh(x) as int;

    function fuh(x: int) : (r: int)

 	lemma split_lemma(x: uint128)
 	 	ensures flh(x) * B() + flh(x) == x;
 	 	ensures flh(x) == x % B();

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

    function interp_half(hr: half_register) : int
    {
        hr[0] as int + hr[1] as int * B()
    }

    method test_half_mul(a : half_register, b : half_register)
        returns (c : half_register, d : half_register)
        ensures interp_half(c) + interp_half(d) * B() * B() == 
            interp_half(a) * interp_half(b);
    {
        var p0 :uint128 := mul_limb(a[0], b[0]);
        var p1 :uint128 := mul_limb(a[1], b[0]);
        var p2 :uint128 := mul_limb(a[0], b[1]);
        var p3 :uint128 := mul_limb(a[1], b[1]);
        
        var t0 : uint128 := uh(p0) as uint128 + lh(p1) as uint128 + lh(p2) as uint128;
        var t1 : uint128 := uh(p1) as uint128 + uh(p2) as uint128 + lh(p3) as uint128 + uh(t0) as uint128;
        assume fuh(p3) + fuh(t1) <= UINT64_MAX as int;
        var t2 : uint64 := uh(p3) + uh(t1);

        c := c[0 := lh(p0)]; 
        c := c[1 := lh(t0)];
        d := c[0 := lh(t1)];
        d := d[1 := t2];

        test_half_mul_lemma(c, d, a, b, p0, p1, p2, p3, t0, t1, t2);
    }

    lemma test_half_mul_lemma(
        c: half_register, d: half_register, a: half_register, b: half_register,
        p0: uint128, p1: uint128, p2: uint128, p3: uint128,
        t0: uint128, t1: uint128, t2: uint64)

        requires c[0] == lh(p0);
        requires c[1] == lh(t0);
        requires d[0] == lh(t1);
        requires d[1] == t2;
        requires t0 == uh(p0) as uint128 + lh(p1) as uint128 + lh(p2) as uint128;
        requires t1 == uh(p1) as uint128 + uh(p2) as uint128 + lh(p3) as uint128 + uh(t0) as uint128;
        requires t2 as int == fuh(p3) + fuh(t1);

        requires p0 == a[0] as int * b[0] as int;
        requires p1 == a[1] as int * b[0] as int;
        requires p2 == a[0] as int * b[1] as int;
        requires p3 == a[1] as int * b[1] as int;

        ensures interp_half(c) + interp_half(d) * B() * B() == 
            interp_half(a) * interp_half(b);
    {
        calc == {
            c[0] as int + c[1] as int * B() + d[0] as int * B() * B() + d[1] as int * B() * B() * B();
            flh(p0) + flh(t0) * B() + flh(t1) * B() * B() + t2 as int * B() * B() * B();
            flh(p0) + flh(t0) * B() + flh(t1) * B() * B() + (uh(p3) + uh(t1)) as int * B() * B() * B();
            flh(p0) + flh(t0) * B() + flh(t1) * B() * B() + fuh(p3) * B() * B() * B() + fuh(t1) * B() * B() * B();
            {
                assume flh(t1) * B() * B() + fuh(t1) * B() * B() * B() == t1 as int * B() * B();
            }
            flh(p0) + flh(t0) * B() + t1 as int * B() * B() + fuh(p3) * B() * B() * B();
            {
                assert t1 as int == fuh(p1) + fuh(p2) + flh(p3) + fuh(t0);
            }
            flh(p0) + flh(t0) * B() + (fuh(p1) + fuh(p2) + flh(p3) + fuh(t0)) * B() * B() + fuh(p3) * B() * B() * B();
            flh(p0) + flh(t0) * B() + fuh(p1) * B() * B() + fuh(p2) * B() * B() + flh(p3) * B() * B() + fuh(t0) * B() * B() + fuh(p3) * B() * B() * B();
            {
                assume flh(p3) * B() * B() + fuh(p3) * B() * B() * B() == p3 as int * B() * B(); 
            }
            flh(p0) + flh(t0) * B() + fuh(p1) * B() * B() + fuh(p2) * B() * B() + fuh(t0) * B() * B() + p3 as int * B() * B();
            {
                assume flh(t0) * B() + fuh(t0) * B() * B() == t0 * B(); 
            }
            flh(p0) + fuh(p1) * B() * B() + fuh(p2) * B() * B() + t0 as int * B() + p3 as int * B() * B();
            {
                assert t0 as int == fuh(p0) + flh(p1) + flh(p2);
            }
            flh(p0) + fuh(p1) * B() * B() + fuh(p2) * B() * B() + (fuh(p0) + flh(p1) + flh(p2)) * B() + p3 as int * B() * B();
            flh(p0) + fuh(p1) * B() * B() + fuh(p2) * B() * B() + fuh(p0) * B() + flh(p1) * B() + flh(p2) * B() + p3 as int * B() * B();
            {
                assume fuh(p2) * B() * B() + flh(p2) * B() == p2 as int * B();
            }
            flh(p0) + fuh(p1) * B() * B() + p2 as int * B() + fuh(p0) * B() + flh(p1) * B() + p3 as int * B() * B();
            {
                assume fuh(p1) * B() * B() + flh(p1) * B() == p1 as int * B();
            }
            flh(p0) + p1 as int * B() + p2 as int * B() + fuh(p0) * B() + p3 as int * B() * B();
            {
                assume fuh(p0) * B() + flh(p0) == p0 as int;
            }
            p0 as int + p1 as int * B() + p2 as int * B() + p3 as int * B() * B();
        }

        assert c[0] as int + c[1] as int * B() + d[0] as int * B() * B() + d[1] as int * B() * B() * B() == 
            p0 as int + p1 as int * B() + p2 as int * B() + p3 as int * B() * B();
        
        calc == {
            interp_half(c) + interp_half(d) * B() * B();
            c[0] as int + c[1] as int * B() + d[0] as int * B() * B() + d[1] as int * B() * B() * B();
            p0 as int + p1 as int * B() + p2 as int * B() + p3 as int * B() * B();
            a[0] as int * b[0] as int +
            a[1] as int * b[0] as int * B() +
            a[0] as int * b[1] as int * B() +
            a[1] as int * b[1] as int * B() * B();
            interp_half(a) * interp_half(b);
        }
    }

    method test_full_mul(a : wide_register, b : wide_register)
    {
        var p0 :uint128 := mul_limb(a[0], b[0]);
        var p1 :uint128 := mul_limb(a[1], b[0]);
        var p2 :uint128 := mul_limb(a[0], b[1]);

        var accu: uint256 := p0 + p1 * B() + p2 * B();
    
        var p3 :uint128 := mul_limb(a[2], b[0]);
        var p4 :uint128 := mul_limb(a[1], b[1]);
        var p5 :uint128 := mul_limb(a[0], b[2]);

        var p6 :uint128 := mul_limb(a[3], b[0]);
        var p7 :uint128 := mul_limb(a[2], b[1]);
        var p8 :uint128 := mul_limb(a[1], b[2]);
        var p9 :uint128 := mul_limb(a[0], b[3]);

        var p10 :uint128 := mul_limb(a[3], b[1]);
        var p11 :uint128 := mul_limb(a[2], b[2]);
        var p12 :uint128 := mul_limb(a[1], b[3]);

        var p13 :uint128 := mul_limb(a[3], b[2]);
        var p14 :uint128 := mul_limb(a[2], b[3]);

        var p15 :uint128 := mul_limb(a[3], b[3]);

    }
}