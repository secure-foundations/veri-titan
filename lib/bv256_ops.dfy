include "generic_bv_ops.dfy"

module bv256_seq refines LittleEndianNat
{
    import integers
 
    function method BASE(): nat
    {
        integers.BASE_256
    }
}

module bv256_ops refines generic_bv_ops
{
    import opened BVSEQ = bv256_seq 

    function method HW_BASE(): nat
    {
        integers.BASE_128
    }

    function method {:opaque} and(x: uint, y: uint): uint
    {
        (x as bv256 & y as bv256) as uint
    }

    function method {:opaque} or(x: uint, y: uint): uint
    {
       (x as bv256 | y as bv256) as uint
    }

    function method {:opaque} not(x: uint) : uint
    {
        !(x as bv256) as uint
    }

    function method {:opaque} xor(x: uint, y: uint): uint
    {
       (x as bv256 ^ y as bv256) as uint
    }

    predicate valid_shift(amount: uint)
    {
        amount <= 256
    }

    function method {:opaque} rs(x: uint, amount: uint): uint
    {
        (x as bv256 >> amount) as uint
    }

    function method {:opaque} ls(x: uint, amount: uint): uint
    {
        (x as bv256 << amount) as uint
    }

    lemma {:axiom} ls_is_mul(x: uint, num_bytes: integers.uint5, r: uint)
        requires r == ls(x, num_bytes * 8);
        ensures (num_bytes == 0) ==> r == x;
        ensures (num_bytes == 8 && x < integers.BASE_192) ==> (r == x * integers.BASE_64);
        ensures (num_bytes == 16 && x < integers.BASE_128) ==> (r == x * integers.BASE_128);
        ensures (num_bytes == 24 && x < integers.BASE_64) ==> (r == x * integers.BASE_192);

    function method {:opaque} msb(x: uint): uint1
    {
        if ((x as bv256 >> 255) & 1 == 1) then 1 else 0
    }

    function method {:opaque} eighth_split(x: uint, sel: nat): integers.uint32
        requires 0 <= sel <= 7
    {
        if sel == 7 then ((x as bv256 >> 224) as int) % integers.BASE_32
        else if sel == 6 then ((x as bv256 >> 192) as int) % integers.BASE_32
        else if sel == 5 then ((x as bv256 >> 160) as int) % integers.BASE_32
        else if sel == 4 then ((x as bv256 >> 128) as int) % integers.BASE_32
        else if sel == 3 then ((x as bv256 >> 96) as int) % integers.BASE_32
        else if sel == 2 then ((x as bv256 >> 64) as int) % integers.BASE_32
        else if sel == 1 then ((x as bv256 >> 32) as int) % integers.BASE_32
        else ((x as bv256) as int) % integers.BASE_32
    }

    function method {:opaque} eighth_assemble(
        p0: integers.uint32, p1: integers.uint32,
        p2: integers.uint32, p3: integers.uint32,
        p4: integers.uint32, p5: integers.uint32,
        p6: integers.uint32, p7: integers.uint32): uint
    {
        ((p7 as bv256 << 224)
        | (p6 as bv256 << 192) 
        | (p5 as bv256 << 160) 
        | (p4 as bv256 << 128) 
        | (p3 as bv256 << 96) 
        | (p2 as bv256 << 64) 
        | (p1 as bv256 << 32) 
        | (p0 as bv256)) as uint
    }

    lemma {:axiom} eighth_value(v: uint)
        ensures v == eighth_assemble(
            eighth_split(v, 0),
            eighth_split(v, 1),
            eighth_split(v, 2),
            eighth_split(v, 3),
            eighth_split(v, 4),
            eighth_split(v, 5),
            eighth_split(v, 6),
            eighth_split(v, 7))
    
    lemma single_digit_lemma_0(a: nat, b: nat, u: nat)
        requires a <= u;
        requires b <= u;
        ensures a * b <= u * u;
}
