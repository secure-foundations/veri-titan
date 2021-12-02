include "../../std_lib/src/Collections/Sequences/LittleEndianNat.dfy"

// refine a big nat module to 32 bits
module bv32_seq refines LittleEndianNat
{
    function method BASE(): nat
    {
        0x100000000
    }
}

// refine a big nat module to 256 bits
module bv256_seq refines LittleEndianNat
{
    function method BASE(): nat
    {
        0x10000000000000000000000000000000000000000000000000000000000000000
    }
}

// decleare generic bitvector operations
// define (some but not all) operations
abstract module generic_bv_ops
{
    import opened LEN: LittleEndianNat

    type uint1   = i :int | 0 <= i < 2

    function method uint_xor(x: uint, y: uint): uint

    function method uint_addc(x: uint, y: uint, cin: uint1): (uint, uint1)
    {
        var sum : int := x + y + cin;
        var sum_out := if sum < BASE() then sum else sum - BASE();
        var cout := if sum  < BASE() then 0 else 1;
        (sum_out, cout)
    }
} 

// refine generic bitvector operations to 32 bits
module bv32_ops refines generic_bv_ops
{
    import opened LEN = bv32_seq

    // implementation for the xor 
    function method {:opaque} uint_xor(x: uint, y: uint): uint
    {
        (x as bv32 ^ y as bv32) as uint
    }
}

// refine generic bitvector operations to 256 bits
module bv256_ops refines generic_bv_ops
{
    import opened LEN = bv256_seq

    // implementation for the xor 
    function method {:opaque} uint_xor(x: uint, y: uint): uint
    {
        (x as bv256 ^ y as bv256) as uint
    }
}

// decleare and define a generic callee function
abstract module generic_callee
{
    import opened GBV: generic_bv_ops

    type uint = GBV.LEN.uint

    function method callee(x: uint, y: uint): uint
    {
        uint_xor(x, uint_addc(x, y, 0))
    }
}

// refine callee function to 32 bits
module bv32_callee refines generic_callee
{
    import opened GBV = bv32_ops
    // this should instantiate a compilable callee function
    
}

// refine callee function to 256 bits
module bv256_callee refines generic_callee
{
    import opened GBV = bv256_ops
    // this should instantiate a compilable callee function
}

// decleare and define a generic caller function
abstract module generic_caller
{
    import opened GCALEE: generic_callee
    type uint = GBV.LEN.uint

    function method caller(x: uint): uint
    {  
        // we can call the callee function
        callee(x, x)
    }
}

// refine caller function to 32 bits
module bv32_caller refines generic_caller
{
    import opened GCALEE = bv32_callee
    type uint32 = GBV.LEN.uint

    function method do_more(x: uint32): uint32
    {
        // we can call the callee function (now concrete)
        var y := callee(x, x);
        // we can call the caller function (now also concrete)
        caller(y)
    }
}

// refine caller function to 256 bits
module bv256_caller refines generic_caller
{
    import opened GCALEE = bv256_callee
    type uint256 = GBV.LEN.uint

    function method do_more(x: uint256): uint256
    {
        // we can call the callee function (now concrete)
        var y := callee(x, x);
        // we can call the caller function (now also concrete)
        caller(y)
    }
}