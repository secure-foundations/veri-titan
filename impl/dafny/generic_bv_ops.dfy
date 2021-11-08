include "../../std_lib/src/Collections/Sequences/LittleEndianNat.dfy"

abstract module generic_bv_ops
{
    import opened BVSEQ: LittleEndianNat
    import Mul

    type uint1   = i :int | 0 <= i < 2
    
    // half word base
    function method HW_BASE(): nat
        ensures HW_BASE() > 1
        ensures HW_BASE() * HW_BASE() == BASE()

    // double word base
    function method DW_BASE(): nat
    {
        Mul.LemmaMulStrictlyPositiveAuto();
        BASE() * BASE()
    }

    function method bool_to_uint1(i:bool) : uint1
    {
        if i then 1 else 0
    }

    function method uint_addc(x: uint, y: uint, cin: uint1): (uint, uint1)
    {
        var sum : int := x + y + cin;
        var sum_out := if sum < BASE() then sum else sum - BASE();
        var cout := if sum  < BASE() then 0 else 1;
        (sum_out, cout)
    }

    function method uint_add(x: uint, y: uint): uint
    {
        uint_addc(x, y, 0).0
    }

    function method uint_subb(x: uint, y: uint, bin: uint1): (uint, uint1)
    {
        var diff : int := x - y - bin;
        var diff_out := if diff >= 0 then diff else diff + BASE();
        var bout := if diff >= 0 then 0 else 1;
        (diff_out, bout)
    }

    function method uint_sub(x: uint, y: uint) : uint
    {
        uint_subb(x, y, 0).0
    }

    function method uint_and(x: uint, y: uint): uint

    function method uint_or(x: uint, y: uint): uint

    function method uint_not(x: uint) : uint

    function method uint_xor(x: uint, y: uint): uint

    function method uint_rs(x: uint, amount: uint): uint

    function method uint_ls(x: uint, amount: uint): uint
} 