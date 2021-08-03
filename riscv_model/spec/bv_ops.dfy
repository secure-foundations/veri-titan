include "rv_consts.dfy"
include "../lib/powers.dfy"

module bv_ops {
    import opened rv_consts
    import opened powers
    import opened congruences

    type uint1   = i :int | 0 <= i < BASE_1
    type uint2   = i :int | 0 <= i < BASE_2
    type uint4   = i :int | 0 <= i < BASE_4
    type uint5   = i :int | 0 <= i < BASE_5
    type uint8   = i :int | 0 <= i < BASE_8
    type uint16  = i :int | 0 <= i < BASE_16
    type uint32  = i :int | 0 <= i < BASE_32
    type uint64  = i :int | 0 <= i < BASE_64
    type uint128 = i :int | 0 <= i < BASE_128
    type uint256 = i :int | 0 <= i < BASE_256
    type uint512 = i :int | 0 <= i < BASE_512

    type int12   = i :int | -2048 <= i <= 2047

    function pow_B32(e: nat): nat
    {
        power(BASE_32, e)
    }

    function bool_to_uint1(i:bool) : uint1
    {
        if i then 1 else 0
    }

    function method {:opaque} uint32_and(x:uint32, y:uint32) : uint32
    {
        (x as bv32 & y as bv32) as uint32
    }

    function method {:opaque} uint32_or(x:uint32, y:uint32):uint32
    {
        (x as bv32 | y as bv32) as uint32
    }

    function method {:opaque} uint32_not(x:uint32) : uint32
    {
        !(x as bv32) as uint32
    }

    function method {:opaque} uint32_xor(x:uint32, y:uint32) : uint32
    {
        (x as bv32 ^ y as bv32) as uint32
    }

    function method {:opaque} uint32_rs(x:uint32, amount:uint32) : uint32
        requires amount < 32;
    {
        (x as bv32 >> amount) as uint32
    }

    function method {:opaque} uint32_ls(x:uint32, amount:uint32) : uint32
        requires amount < 32;
    {
        (x as bv32 << amount) as uint32
    }

    function method {:opaque} uint32_add(x:uint32, y:uint32):uint32
    {
        var r := x as int + y as int;
        if r >= BASE_32 then (r - BASE_32) else r
    }

    function method {:opaque} uint32_sub(x:uint32, y:uint32) : uint32
    {
        (x - y) % BASE_32
    }

    function method uint32_full_mul(x:uint32, y:uint32): (r: uint64)
        ensures r == x * y
    {
        single_digit_lemma_0(x, y, BASE_32-1);
        x * y
    }

    function method uint32_mul(x:uint32, y:uint32) : uint32
    {
      uint64_lh(uint32_full_mul(x, y))
    }

    function method uint32_mulhu(x:uint32, y:uint32) : uint32
    {
      uint64_uh(uint32_full_mul(x, y))
    }

    function uint32_lt(x:uint32, y:uint32) : uint32
    {
        if x < y then 1 else 0
    }
    
    lemma single_digit_lemma_0(a: nat, b: nat, u: nat)
        requires a <= u;
        requires b <= u;
        ensures a * b <= u * u;
    {
        assert true;
    }

    lemma single_digit_lemma_1(a: nat, b: nat, c: nat, u: nat)
        requires a <= u;
        requires b <= u;
        requires c <= u;
        ensures a * b + c < (u + 1) * (u + 1);
    {
        calc {
            a * b + c;
            <= { single_digit_lemma_0(a, b, u); }
            u * u + c;
            <= u * u + u;
            u * (u + 1);
            < (u + 1) * (u + 1);
        }
    }

    lemma single_digit_lemma_2(a: nat, b: nat, c: nat, d: nat, u: nat)
        requires a <= u;
        requires b <= u;
        requires c <= u;
        requires d <= u;
        ensures a * b + c + d < (u + 1) * (u + 1);
    {
        calc {
            a * b + c + d;
            <={ single_digit_lemma_0(a, b, u); }
            u * u + c + d;
            <= u * u + u + u;
            u * u + 2 * u;
            < u * u + 2 * u + 1;
            (u + 1) * (u + 1);
        }
    }

    function method {:opaque} uint64_lh(x: uint64): uint32
    {
        x % BASE_32
    }

    function method {:opaque} uint64_uh(x: uint64): uint32
    {
        x / BASE_32
    }

    lemma lemma_uint64_half_split(x: uint64)
        ensures x == uint64_lh(x) + uint64_uh(x) * BASE_32;
    {
        reveal uint64_lh();
        reveal uint64_uh();
    }

    
} // end module ops
