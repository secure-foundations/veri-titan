include "rv_consts.dfy"

include "../../standard_libraries/src/BoundedInts.dfy"  
include "../../standard_libraries/src/NonlinearArithmetic/DivMod.dfy"
include "../../standard_libraries/src/NonlinearArithmetic/Mul.dfy"
include "../../standard_libraries/src/NonlinearArithmetic/Power.dfy"
include "../../standard_libraries/src/NonlinearArithmetic/Power2.dfy"

module bv_ops {
    import opened Power
    import opened Power2
    import opened Mul
    import opened DivMod

    import opened BoundedInts
    import opened rv_consts

    type uint1    = x: int | 0 <= x < BoundedInts.TWO_TO_THE_1
    type uint2    = x: int | 0 <= x < BoundedInts.TWO_TO_THE_2
    type uint4    = x: int | 0 <= x < BoundedInts.TWO_TO_THE_4
    type uint5    = x: int | 0 <= x < BoundedInts.TWO_TO_THE_5
    type uint8    = x: int | 0 <= x < BoundedInts.TWO_TO_THE_8
    type uint16   = x: int | 0 <= x < BoundedInts.TWO_TO_THE_16
    type uint24   = x: int | 0 <= x < BoundedInts.TWO_TO_THE_24
    type uint32   = x: int | 0 <= x < BoundedInts.TWO_TO_THE_32
    type uint64   = x: int | 0 <= x < BoundedInts.TWO_TO_THE_64
    type uint128  = x: int | 0 <= x < BoundedInts.TWO_TO_THE_128
    type uint256  = x: int | 0 <= x < BoundedInts.TWO_TO_THE_256
    type uint512  = x: int | 0 <= x < BoundedInts.TWO_TO_THE_512

    type int12  = i :int | -2048 <= i <= 2047

    type int32  = i :int | -BASE_31 <= i <= (BASE_31 - 1)
    type int64  = i :int | -BASE_63 <= i <= (BASE_63 - 1)


    lemma div_bound(x: int, n: nat)
      requires n > 0
      ensures x >= 0 ==> 0 <= x/n <= x
      ensures x < 0 ==> 0 > (x/n) >= x
    {
      if x >= 0 {
        LemmaDivNonincreasingAuto();
        LemmaDivPosIsPosAuto();
      } else {
        assume false; // TODO
      }
    }

    /* signed operations */
    function method int32_rs(x: int32, shift: nat) : int32
    {
      div_bound(x, Pow2(shift));
      x / Pow2(shift)
    }

    // right arithmetic shift
    function method int64_rs(x: int64, shift: nat) : int64
    {
      div_bound(x, Pow2(shift));
      x / Pow2(shift)
    }

    function method to_uint32(i: int) : uint32
      requires - BASE_32 < i < BASE_32
    {
      if i < 0 then i + BASE_32 else i
    }

    function method to_int32(i:uint32) : int32
    {
      if i > (BASE_31 - 1) then i - BASE_32 else i
    }


    lemma int32_uint32_inverse_lemma(i:int32)
      ensures to_int32(to_uint32(i)) == i
    {
    }

    lemma uint32_int32_inverse_lemma(i:uint32)
      ensures to_uint32(to_int32(i)) == i
    {
    }

    function int32_lt(x: int32, y: int32) : uint32
    {
      if x < y then 1 else 0
    }

    function method to_uint64(i: int) : uint64
      requires - BASE_64 < i < BASE_64
    {
      if i < 0 then i + BASE_64 else i
    }

    function method to_int64(i:uint64) : int64
    {
      if i > (BASE_63 - 1) then i - BASE_64 else i
    }


    lemma int64_uint64_inverse_lemma(i:int64)
      ensures to_int64(to_uint64(i)) == i
    {
    }

    lemma uint64_int64_inverse_lemma(i:uint64)
      ensures to_uint64(to_int64(i)) == i
    {
    }


    function pow_B32(e: nat): nat
    {
        LemmaPowPositiveAuto();
        Pow(BASE_32, e)
    }

    function bool_to_uint1(i:bool) : uint1
    {
        if i then 1 else 0
    }

    function neg1_to_uint1(i:int) : uint1
      requires -1 <= i <= 0;
    {
      if i == -1 then 1 else 0
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

    function method uint32_add(x:uint32, y:uint32):uint32
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
        LemmaMulNonnegative(x, y);
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
      LemmaMulUpperBoundAuto();
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
            <= { single_digit_lemma_0(a, b, u); }
            u * u + c + d;
            <= u * u + u + u;
            u * u + 2 * u;
            < (u * u) + (2 * u) + 1;
        }

        calc {
            (u + 1) * (u + 1);
            { LemmaMulIsDistributiveAdd(u + 1, u, 1); }
            (u + 1) * u + (u + 1) * 1; 
            u * (u + 1) + u + 1;
            { LemmaMulIsDistributiveAdd(u, u, 1); }
            (u * u) + (2 * u) + 1;
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

    function method uint32_subb(x: uint32, y: uint32, bin: uint1): (uint32, uint1)
    {
      var diff : int := x - y - bin;
        var diff_out := if diff >= 0 then diff else diff + BASE_32;
        var bout := if diff >= 0 then 0 else 1;
        (diff_out, bout)
    }

    // signed integer views
    function method {:opaque} int64_lh(x: int64): uint32
    {
        to_uint64(x) % BASE_32
    }

    function method {:opaque} int64_uh(x: int64): uint32
    {
        to_uint64(x) / BASE_32
    }

    lemma lemma_int64_half_split(x: int64)
        ensures x == to_int64(int64_lh(x) + int64_uh(x) * BASE_32);
    {
        reveal int64_lh();
        reveal int64_uh();
    }

} // end module ops
