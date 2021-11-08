include "generic_bv_ops.dfy"

module bv32_seq refines LittleEndianNat
{
    import integers

    function method BASE(): nat
    {
        integers.BASE_32
    }
}

module bv32_ops refines generic_bv_ops
{
    import opened BVSEQ = bv32_seq 

    // half word base
    function method HW_BASE(): nat
    {
        integers.BASE_16
    }

    function method {:opaque} and(x: uint, y: uint): uint
    {
        (x as bv32 & y as bv32) as uint
    }

    function method {:opaque} or(x: uint, y: uint): uint
    {
       (x as bv32 | y as bv32) as uint
    }

    function method {:opaque} not(x: uint) : uint
    {
        !(x as bv32) as uint
    }

    function method {:opaque} xor(x: uint, y: uint): uint
    {
       (x as bv32 ^ y as bv32) as uint
    }

    predicate valid_shift(amount: uint)
    {
        amount <= 32
    }

    function method {:opaque} rs(x: uint, amount: uint): uint
    {
        (x as bv32 >> amount) as uint
    }

    function method {:opaque} ls(x: uint, amount: uint): uint
    {
        (x as bv32 << amount) as uint
    }
} 