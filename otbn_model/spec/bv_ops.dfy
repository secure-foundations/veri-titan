include "vt_consts.dfy"
include "../lib/powers.dfy"

module bv_ops {
	import opened vt_consts
	import opened powers

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
		(x + y) % BASE_32
	}

	function method {:opaque} uint32_sub(x:uint32, y:uint32):uint32
	{
		(x - y) % BASE_32
	}

	function method {:opaque} uint32_se(x:uint32, size:int):uint32
		requires 0 <= size < 32;

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

	function method {:opaque} uint256_ls(x: uint256, num_bytes: int): (r: uint256)
		requires 0 <= num_bytes < 32;
		ensures (num_bytes == 0) ==> r == x;
		ensures (num_bytes == 8 && x < BASE_192) ==> (r == x * BASE_64);
	{
		assume false;
		(x as bv256 << (num_bytes * 8)) as uint256
	}

	function method {:opaque} uint256_rs(x: uint256, num_bytes: int): uint256
		requires 0 <= num_bytes < 32;
		ensures uint256_rs(x, 0) == x;
	{
		assume false;
		(x as bv256 >> (num_bytes * 8)) as uint256
	}

	function method uint256_sb(b:uint256, st: bool, sb: uint32) : uint256
		requires sb < 32;
	{	
		if sb == 0 then b
		else if st then uint256_ls(b, sb)
		else uint256_rs(b, sb)
	}

	function method {:opaque} uint256_lh(x: uint256): uint128
	{
		x % BASE_128
	}

	function method {:opaque} uint256_uh(x: uint256): uint128
	{
		x / BASE_128
	}

	function method {:opaque} uint256_hwb(x: uint256, v: uint128, lower: bool): (x': uint256)
		// overwrites the lower half, keeps the higher half
		ensures lower ==> (uint256_lh(x') == v && uint256_uh(x') == uint256_uh(x));
		// overwrites the higher half, keeps the lower half
		ensures !lower ==> (uint256_uh(x') == v && uint256_lh(x') == uint256_lh(x));

	function method {:opaque} uint256_qmul(x: uint256, qx: uint2, y: uint256, qy:uint2): uint128
	{
		assume false; // TODO: add a bound proof
		uint256_qsel(x, qx) * uint256_qsel(y, qy)
	}

	function method {:opaque} uint256_qsel(x: uint256, qx: uint2): uint64
	{
		if qx == 0 then
			x % BASE_64
		else if qx == 1 then
			(x / BASE_64) % BASE_64
		else if qx == 1 then
			(x / BASE_128) % BASE_64
		else
			(x / BASE_192) % BASE_64
	}

    lemma {:axiom} and_single_bit_lemma(x': uint256, x: uint256, w0: uint256, i: nat)
        requires w0 == power(2, i);
        requires x' == uint256_and(x, w0);
        ensures x' == power(2, i) || x' == 0;

    lemma {:axiom} or_zero_nop_lemma(x: uint256, z: uint256)
        requires z == 0;
        ensures uint256_or(x, z) == x;

    lemma {:axiom} or_single_bit_add_lemma(x': uint256, x: uint256, w0: uint256, i: nat)
        requires w0 == power(2, i);
        requires x < power(2, i);
        requires x' == uint256_or(x, w0);
        ensures x' == x + w0;
        ensures x' < power(2, i + 1);

    lemma {:axiom} odd_and_one_lemma(x: uint256) 
        requires x % 2 == 1;
        ensures uint256_and(x, 1) == 1;

	lemma lemma_xor_clear(x: uint256)
	    ensures uint256_xor(x, x) == 0;
	{
		reveal uint256_xor();
	}

	lemma lemma_uint256_hwb(x1: uint256, x2: uint256, x3: uint256, lo: uint128, hi: uint128)
		requires x2 == uint256_hwb(x1, lo, true);
		requires x3 == uint256_hwb(x2, hi, false);
		ensures x3 == lo + hi * BASE_128;
	{
		calc == {
			x3;
			{
				lemma_uint256_half_split(x3);
			}
			uint256_lh(x3) + uint256_uh(x3) * BASE_128;
			{
				assert uint256_uh(x3) == hi && uint256_lh(x3) == uint256_lh(x2);
			}
			uint256_lh(x2) + hi * BASE_128;
			{
				assert uint256_lh(x2) == lo;
			}
			lo + hi * BASE_128;
		}
	}

	lemma lemma_uint256_half_split(x: uint256)
		ensures x == uint256_lh(x) + uint256_uh(x) * BASE_128;
	{
		reveal uint256_lh();
		reveal uint256_uh();
	}

	lemma lemma_uint256_quarter_split(x: uint256)
		ensures x == uint256_qsel(x, 0) +
			uint256_qsel(x, 1) * BASE_64 + 
			uint256_qsel(x, 2) * BASE_128 + 
			uint256_qsel(x, 3) * BASE_192;
	{
		// reveal uint256_qsel(); // TODO: revaling is not sufficient
		assume false;
	}
} // end module ops
