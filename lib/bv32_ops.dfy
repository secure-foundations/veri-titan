include "generic_bv_ops.dfy"
include "DivModNeg.dfy"
include "../std_lib/src/NonlinearArithmetic/Power2.dfy"
include "bv16_ops.dfy"

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
    import DivModNeg
    import bv16_ops

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

    function method {:opaque} msb(x: uint): uint1
    {
        if ((x as bv32 >> 32) & 1 == 1) then 1 else 0
    }

    function uint32_lt(x: uint, y: uint): uint
    {
        if x < y then 1 else 0
    }

    function uint32_le(x: uint, y: uint): uint
    {
      if x <= y then 1 else 0
    }

    // function method uint32_full_mul(x: uint, y: uint): (r: nat)
    //     ensures r == x * y
    //     ensures r < DW_BASE()
    // {
    //     x * y
    // }

    function method uint16_sign_ext(x: integers.uint16): uint
    {
        var s := bv16_ops.to_int16(x);
        if s < 0 then x + 0xffff0000 else x
    }

    function method uint32_mul(x: uint, y: uint): uint
    {
        mul(x, y)
    }

    function method uint32_mulhu(x: uint, y: uint): uint
    {
        full_mul_bound_lemma(x, y);
        dw_uh(x * y)
    }

    function method uint32_add(x: uint, y: uint): uint
    {
        add(x, y)
    }

    function method to_uint32(x: sint): uint
    {
        to_2s_comp(x)
    }

    function method to_int32(x: uint): sint
    {
        if x < integers.BASE_31 then x else x - integers.BASE_32
    }

    lemma signed_conversion_lemma(x: sint)
        ensures to_int32(to_uint32(x)) == x
    {
    }

    function method int32_rs(x: sint, shift: nat) : sint
    {
        DivModNeg.LemmaDivBounded(x, Power2.Pow2(shift));
        x / Power2.Pow2(shift)
    }

    function method uint32_ls(x: uint, amount: uint) : (r: uint)
        requires amount < 32;
    {
        ls(x, amount)
    }

    function method uint32_xor(x: uint, y: uint): uint
    {
        xor(x, y)
    }

    function method uint32_or(x: uint, y: uint): uint
    {
        or(x, y)
    }

    function method uint32_and(x: uint, y: uint): uint
    {
        and(x, y)
    }

    function method uint32_rs(x: uint, amount: uint): uint
        requires amount < 32;
    {
        rs(x, amount)
    }

    function method uint32_sub(x: uint, y: uint): uint
    {
        sub(x, y)
    }

    function method uint32_rsai(x: uint, amount: uint): uint
        requires amount < 32;
    {
        to_uint32(int32_rs(to_int32(x), amount))
    }

    function method uint32_lh(x: uint): integers.uint16
    {
        lh(x)
    }

    function method uint32_uh(x: uint): integers.uint16
    {
        uh(x)
    }
}
