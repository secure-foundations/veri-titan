include "bv_op.s.dfy"

module bv16_seq refines LittleEndianNat
{
    import integers

    function method BASE(): nat
    {
        integers.BASE_16
    }
}

module bv16_op_s refines bv_op_s
{
    import opened BVSEQ = bv16_seq
    import DivModNeg

    // half word base
    function method HW_BASE(): nat
    {
        integers.BASE_8
    }

    function method {:opaque} and(x: uint, y: uint): uint
    {
        (x as bv16 & y as bv16) as uint
    }

    function method {:opaque} or(x: uint, y: uint): uint
    {
       (x as bv16 | y as bv16) as uint
    }

    function method {:opaque} not(x: uint) : uint
    {
        !(x as bv16) as uint
    }

    function method {:opaque} xor(x: uint, y: uint): uint
    {
       (x as bv16 ^ y as bv16) as uint
    }

    predicate valid_shift(amount: uint)
    {
        amount <= 16
    }

    function method {:opaque} rs(x: uint, amount: uint): uint
    {
        (x as bv16 >> amount) as uint
    }

    function method {:opaque} ls(x: uint, amount: uint): uint
    {
        (x as bv16 << amount) as uint
    }

    function method {:opaque} msb(x: uint): uint1
    {
        if ((x as bv256 >> 16) & 1 == 1) then 1 else 0
    }

    function uint16_lt(x: uint, y: uint): uint
    {
        if x < y then 1 else 0
    }

    function uint16_le(x: uint, y: uint): uint
    {
      if x <= y then 1 else 0
    }

    function method uint16_mul(x: uint, y: uint): uint
    {
        mul(x, y)
    }

    function method uint16_mulhu(x: uint, y: uint): uint
    {
        full_mul_bound_lemma(x, y);
        dw_uh(x * y)
    }

    function method uint16_add(x: uint, y: uint): uint
    {
        add(x, y)
    }

    function method to_uint16(x: sint): uint
    {
        to_2s_comp(x)
    }

    function method to_int16(x: uint): sint
    {
        if x <  32768 then x else x - 65536
    }

    lemma signed_conversion_lemma(x: sint)
        ensures to_int16(to_uint16(x)) == x
    {
    }

    function method int16_rs(x: sint, shift: nat) : sint
    {
        DivModNeg.LemmaDivBounded(x, Power2.Pow2(shift));
        x / Power2.Pow2(shift)
    }

    function method uint16_ls(x: uint, amount: uint) : (r: uint)
        requires amount < 16;
    {
        ls(x, amount)
    }

    function method uint16_xor(x: uint, y: uint): uint
    {
        xor(x, y)
    }

    function method uint16_or(x: uint, y: uint): uint
    {
        or(x, y)
    }

    function method uint16_and(x: uint, y: uint): uint
    {
        and(x, y)
    }

    function method uint16_rs(x: uint, amount: uint): uint
        requires amount < 16;
    {
        rs(x, amount)
    }

    function method uint16_sub(x: uint, y: uint): uint
    {
        sub(x, y)
    }
}
        
