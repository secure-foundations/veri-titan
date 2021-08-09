include "vt_consts.dfy"
include "../lib/powers.dfy"

module bv_ops {
    import opened vt_consts
    import opened powers
    import opened congruences

    type uint1   = i :int | 0 <= i < BASE_1
    type uint2   = i :int | 0 <= i < BASE_2
    type uint4   = i :int | 0 <= i < BASE_4
    type uint5   = i :int | 0 <= i < BASE_5
    type uint8   = i :int | 0 <= i < BASE_8
    type uint10  = i :int | 0 <= i < 1024
    type uint16  = i :int | 0 <= i < BASE_16
    type uint32  = i :int | 0 <= i < BASE_32
    type uint64  = i :int | 0 <= i < BASE_64
    type uint128 = i :int | 0 <= i < BASE_128
    type uint256 = i :int | 0 <= i < BASE_256
    type uint512 = i :int | 0 <= i < BASE_512

    type int10   = i :int | -512 <= i <= 511
    type int12   = i :int | -2048 <= i <= 2047

    datatype shift_t = SFT(left: bool, bytes: uint5)

    const SFT_DFT :shift_t := SFT(true, 0);

    predicate cong_B256(a: int, b: int)
    {
        cong(a, b, BASE_256)
    }

    function pow_B256(e: nat): nat
    {
        power(BASE_256, e)
    }

    function method bool_to_uint1(i:bool) : uint1
    {
        if i then 1 else 0
    }

    function method to_2s_comp_uint32(n: int): uint32
        requires - BASE_32 < n < BASE_32
    {
        if n < 0 then n + BASE_32 else n
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

    function method uint32_add(x:uint32, y:uint32): uint32
    {
        var s: uint64 := x + y;
        if s < BASE_32 then 
            s
        else
            s - BASE_32
    }

    function method uint32_addi(x: uint32, imm: int): uint32
        requires - BASE_32 < imm < BASE_32
    {
        uint32_add(x, to_2s_comp_uint32(imm))
    }

    function method {:opaque} uint32_sub(x:uint32, y:uint32):uint32
    {
        (x - y) % BASE_32
    }

    function method uint256_msb(x: uint256): uint1

    function method uint256_lsb(x: uint256): uint1

    function method uint256_mul(x: uint256, y: uint256): uint256
    {
        (x * y) % BASE_256
    }

    function method uint256_addc(x: uint256, y: uint256, cin: uint1): (uint256, uint1)
    {
        var sum : int := x + y + cin;
        var sum_out := if sum < BASE_256 then sum else sum - BASE_256;
        var cout := if sum  < BASE_256 then 0 else 1;
        (sum_out, cout)
    }

    lemma uint256_addc_cong_lemma(z: uint256, x: uint256, y: uint256)
        requires uint256_addc(x, y, 0).0 == z;
        ensures cong_B256(z, x + y);
    {
        reveal cong();
    }

    function method uint256_subb(x: uint256, y: uint256, bin: uint1): (uint256, uint1)
    {
      var diff : int := x - y - bin;
        var diff_out := if diff >= 0 then diff else diff + BASE_256;
        var bout := if diff >= 0 then 0 else 1;
        (diff_out, bout)
    }

    function method {:opaque} uint256_xor(x: uint256, y: uint256): uint256
    {
        (x as bv256 ^ y as bv256) as uint256
    }

    function method {:opaque} uint256_or(x: uint256, y: uint256): uint256
    {
        (x as bv256 | y as bv256) as uint256
    }
    
    function method {:opaque} uint256_and(x: uint256, y: uint256): uint256
    {
        (x as bv256 | y as bv256) as uint256
    }

    function method uint256_ls(x: uint256, num_bytes: uint5): (r: uint256)
        ensures (num_bytes == 0) ==> r == x;
        ensures (num_bytes == 8 && x < BASE_192) ==> (r == x * BASE_64);
        ensures (num_bytes == 16 && x < BASE_128) ==> (r == x * BASE_128);
        ensures (num_bytes == 24 && x < BASE_64) ==> (r == x * BASE_192);
    {
        assume false;
        (x as bv256 << (num_bytes * 8)) as uint256
    }

    function method uint256_rs(x: uint256, num_bytes: uint5): uint256

    function method uint256_sb(b: uint256, shift: shift_t) : uint256
    {    
        var count := shift.bytes;
        if count == 0 then b
        else if shift.left then uint256_ls(b, count)
        else uint256_rs(b, count)
    }

    function method {:opaque} uint256_lh(x: uint256): uint128
    {
        x % BASE_128
    }

    function method {:opaque} uint256_uh(x: uint256): uint128
    {
        x / BASE_128
    }

    lemma uint256_half_split_lemma(x: uint256)
        ensures x == uint256_lh(x) + uint256_uh(x) * BASE_128;
    {
        reveal uint256_lh();
        reveal uint256_uh();
    }

    function method {:extern} uint256_hwb(x: uint256, v: uint128, lower: bool): (x': uint256)
        // overwrites the lower half, keeps the higher half
        ensures lower ==> (uint256_lh(x') == v && uint256_uh(x') == uint256_uh(x));
        // overwrites the higher half, keeps the lower half
        ensures !lower ==> (uint256_uh(x') == v && uint256_lh(x') == uint256_lh(x));

    lemma uint256_hwb_lemma(x1: uint256, x2: uint256, x3: uint256, lo: uint128, hi: uint128)
        requires x2 == uint256_hwb(x1, lo, true);
        requires x3 == uint256_hwb(x2, hi, false);
        ensures x3 == lo + hi * BASE_128;
    {
        calc == {
            x3;
                { uint256_half_split_lemma(x3); }
            uint256_lh(x3) + uint256_uh(x3) * BASE_128;
                { assert uint256_uh(x3) == hi && uint256_lh(x3) == uint256_lh(x2); }
            uint256_lh(x2) + hi * BASE_128;
                { assert uint256_lh(x2) == lo; }
            lo + hi * BASE_128;
        }
    }

    lemma single_digit_lemma_0(a: nat, b: nat, u: nat)
        requires a <= u;
        requires b <= u;
        ensures a * b <= u * u;
    {
        calc <= {
            a * b;
            a * u;
            u * u;
        }
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

    function method {:opaque} uint256_qsel(x: uint256, qx: uint2): uint64
    {
        if qx == 0 then
            uint256_lh(x) % BASE_64
        else if qx == 1 then
            uint256_lh(x) / BASE_64
        else if qx == 2 then
            uint256_uh(x) % BASE_64
        else
            uint256_uh(x) / BASE_64
    }

    function method {:opaque} uint256_qmul(x: uint256, qx: uint2, y: uint256, qy: uint2): uint128
    {
        var src1 := uint256_qsel(x, qx);
        var src2 := uint256_qsel(y, qy);
        single_digit_lemma_0(src1, src2, BASE_64-1);
        src1 as uint128 * src2 as uint128
    }

    lemma uint256_quarter_split_lemma(x: uint256)
        ensures x == uint256_qsel(x, 0) +
            uint256_qsel(x, 1) * BASE_64 + 
            uint256_qsel(x, 2) * BASE_128 + 
            uint256_qsel(x, 3) * BASE_192;
    {
        reveal uint256_qsel();
        assert uint256_qsel(x, 0) + uint256_qsel(x, 1) * BASE_64 == uint256_lh(x);
        assert uint256_qsel(x, 2) + uint256_qsel(x, 3) * BASE_64 == uint256_uh(x);

        calc == {
            uint256_qsel(x, 0) + uint256_qsel(x, 1) * BASE_64 + uint256_qsel(x, 2) * BASE_128 + uint256_qsel(x, 3) * BASE_192;
             uint256_lh(x) + uint256_qsel(x, 2) * BASE_128 + uint256_qsel(x, 3) * BASE_192;
             uint256_lh(x) + (uint256_qsel(x, 2) + uint256_qsel(x, 3) * BASE_64) * BASE_128;
             uint256_lh(x) + uint256_uh(x) * BASE_128;
                 { reveal uint256_lh(); reveal uint256_uh(); }
            x;
        }
    }

    // lemma {:axiom} and_single_bit_lemma(x': uint256, x: uint256, w0: uint256, i: nat)
    //     requires w0 == power(2, i);
    //     requires x' == uint256_and(x, w0);
    //     ensures x' == power(2, i) || x' == 0;

    // lemma {:axiom} or_zero_nop_lemma(x: uint256, z: uint256)
    //     requires z == 0;
    //     ensures uint256_or(x, z) == x;

    // lemma {:axiom} or_single_bit_add_lemma(x': uint256, x: uint256, w0: uint256, i: nat)
    //     requires w0 == power(2, i);
    //     requires x < power(2, i);
    //     requires x' == uint256_or(x, w0);
    //     ensures x' == x + w0;
    //     ensures x' < power(2, i + 1);

    // lemma {:axiom} odd_and_one_lemma(x: uint256) 
    //     requires x % 2 == 1;
    //     ensures uint256_and(x, 1) == 1;

    lemma xor_clear_lemma(x: uint256)
        ensures uint256_xor(x, x) == 0;
    {
        reveal uint256_xor();
    }

    function method {:opaque} uint512_lh(x: uint512): uint256
    {
        x % BASE_256
    }

    function method {:opaque} uint512_uh(x: uint512): uint256
    {
        x / BASE_256
    }

    lemma lemma_uint512_half_split(x: uint512)
        ensures x == uint512_lh(x) + uint512_uh(x) * BASE_256;
    {
        reveal uint512_lh();
        reveal uint512_uh();
    }
} // end module ops
