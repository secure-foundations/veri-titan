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
        // ensures interp_half(a) * interp_half(b) == 
            // interp_half(c) * B() * B() + interp_half(d);
    {
        var p0 :uint128 := mul_limb(a[0], b[0]);
        var p1 :uint128 := mul_limb(a[1], b[0]);
        var p2 :uint128 := mul_limb(a[0], b[1]);
        var p3 :uint128 := mul_limb(a[1], b[1]);
        
        var t0 : uint128 := uh(p0) as uint128 + lh(p1) as uint128 + lh(p2) as uint128;
        var t1 : uint128 := uh(p1) as uint128 + uh(p2) as uint128 + lh(p3) as uint128 + uh(t0) as uint128;
        assume uh(p3) as int + uh(t1) as int <= UINT64_MAX as int;
        var t2 : uint64 := uh(p3) + uh(t1);

        c := c[0 := lh(p0)]; 
        c := c[1 := lh(t0)];
        d := c[0 := lh(t1)];
        d := d[1 := t2];

        test_half_mul_lemma_1(c, d, p0, p1, p2, p3, t0, t1, t2);
    }

    lemma test_half_mul_lemma_1(
        c: half_register, d: half_register,
        p0: uint128, p1: uint128, p2: uint128, p3: uint128,
        t0: uint128, t1: uint128, t2: uint64)

        requires c[0] == lh(p0);
        requires c[1] == lh(t0);
        requires d[0] == lh(t1);
        requires d[1] == t2;
        requires t0 == uh(p0) as uint128 + lh(p1) as uint128 + lh(p2) as uint128;
        requires t1 == uh(p1) as uint128 + uh(p2) as uint128 + lh(p3) as uint128 + uh(t0) as uint128;
        requires t2 as int == uh(p3) as int + uh(t1) as int;
    {
        calc == {
            c[0] as int + c[1] as int * B() + d[0] as int * B() * B() + d[1] as int * B() * B() * B();
            lh(p0) as int + lh(t0) as int * B() + lh(t1) as int * B() * B() + t2 as int * B() * B() * B();
            lh(p0) as int + lh(t0) as int * B() + lh(t1) as int * B() * B() + (uh(p3) + uh(t1)) as int * B() * B() * B();
            lh(p0) as int + lh(t0) as int * B() + lh(t1) as int * B() * B() + uh(p3) as int * B() * B() * B() + uh(t1) as int * B() * B() * B();
            {
                assume lh(t1) as int * B() * B() + uh(t1) as int * B() * B() * B() == t1 as int * B() * B();
            }
            lh(p0) as int + lh(t0) as int * B() + t1 as int * B() * B() + uh(p3) as int * B() * B() * B();
            {
                assert t1 as int == uh(p1) as int + uh(p2) as int + lh(p3) as int + uh(t0) as int;
            }
            lh(p0) as int + lh(t0) as int * B() + (uh(p1) as int + uh(p2) as int + lh(p3) as int + uh(t0) as int) * B() * B() + uh(p3) as int * B() * B() * B();
            lh(p0) as int + lh(t0) as int * B() + uh(p1) as int * B() * B() + uh(p2) as int * B() * B() + lh(p3) as int * B() * B() + uh(t0) as int * B() * B() + uh(p3) as int * B() * B() * B();
            {
                assume lh(p3) as int * B() * B() + uh(p3) as int * B() * B() * B() == p3 as int * B() * B(); 
            }
            lh(p0) as int + lh(t0) as int * B() + uh(p1) as int * B() * B() + uh(p2) as int * B() * B() + uh(t0) as int * B() * B() + p3 as int * B() * B();
            {
                assume lh(t0) as int * B() + uh(t0) as int * B() * B() == t0 * B(); 
            }
            lh(p0) as int + uh(p1) as int * B() * B() + uh(p2) as int * B() * B() + t0 as int * B() + p3 as int * B() * B();
            {
                assert t0 as int == uh(p0) as int + lh(p1) as int + lh(p2) as int;
            }
            lh(p0) as int + uh(p1) as int * B() * B() + uh(p2) as int * B() * B() + (uh(p0) as int + lh(p1) as int + lh(p2) as int) * B() + p3 as int * B() * B();
            lh(p0) as int + uh(p1) as int * B() * B() + uh(p2) as int * B() * B() + uh(p0) as int * B() + lh(p1) as int * B() + lh(p2) as int * B() + p3 as int * B() * B();
            {
                assume uh(p2) as int * B() * B() + lh(p2) as int * B() == p2 as int * B();
            }
            lh(p0) as int + uh(p1) as int * B() * B() + p2 as int * B() + uh(p0) as int * B() + lh(p1) as int * B() + p3 as int * B() * B();
            {
                assume uh(p1) as int * B() * B() + lh(p1) as int * B() == p1 as int * B();
            }
            lh(p0) as int + p1 as int * B() + p2 as int * B() + uh(p0) as int * B() + p3 as int * B() * B();
            {
                assume uh(p0) as int * B() + lh(p0) as int == p0 as int;
            }
            p0 as int + p1 as int * B() + p2 as int * B() + p3 as int * B() * B();
        }
    }

    lemma test_half_mul_lemma_2(c: half_register, d: half_register, a: half_register, b: half_register,
        p0: uint128, p1: uint128, p2: uint128, p3: uint128)
        requires
            c[0] as int + c[1] as int * B() + d[0] as int * B() * B() + d[1] as int * B() * B() * B()
            == 
            p0 as int + p1 as int * B() + p2 as int * B() + p3 as int * B() * B();
        // ensures 
        //     a[0] as int * b[0] as int +
        //     a[1] as int * b[0] as int * B() +
        //     a[0] as int * b[1] as int * B() +
        //     a[1] as int * b[1] as int * B() * B();
    {

    }
}