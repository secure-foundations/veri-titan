include "types.dfy"
include "../lib/powers.dfy"

module ops {
	import opened types
	import opened powers

	function pow2(n:nat) : nat {
		if n == 0 then 1 else 2 * pow2(n-1)
	}

	///////////////////////////
	// Operations on bv32s
	///////////////////////////
	function method {:opaque} BitAdd(x:bv32, y:bv32): bv32
	{
		x + y
	}

	function method {:opaque} BitSub(x:bv32, y:bv32): bv32
	{
		x - y
	}

	function method {:opaque} BitAnd(x:bv32, y:bv32): bv32
	{
		x & y
	}

	function method {:opaque} BitOr(x:bv32, y:bv32): bv32
	{
		x | y
	}

	function method {:opaque} BitXor(x:bv32, y:bv32): bv32
	{
		x ^ y
	}

	function method {:opaque} BitMod(x:bv32, y:bv32): bv32
		requires y != 0
	{
		x % y
	}

	function method {:opaque} BitDiv(x:bv32, y:bv32): bv32
		requires y != 0
	{
		x / y
	}

	function method {:opaque} BitMul(x:bv32, y:bv32): bv32
	{
		x * y
	}

	function method {:opaque} BitNot(x:bv32): bv32
	{
		!x
	}

	function method {:opaque} BitShiftLeft(x:bv32, amount:int): bv32
		requires 0 <= amount < 32;
	{
		x << amount
	}

	function method {:opaque} BitShiftRight(x:bv32, amount:int): bv32
		requires 0 <= amount < 32;
	{
		x >> amount
	}

	function method {:opaque} BitRotateRight(x:bv32, amount:int): bv32
		requires 0 <= amount < 32;
	{
		// TODO: Replace with Dafny's builtin operator for this
		(x >> amount) | (x << (32 - amount))
	}

	function method {:opaque} BitRotateLeft(x:bv32, amount:int): bv32
		requires 0 <= amount < 32;
	{
		// TODO: Replace with Dafny's builtin operator for this
		(x << amount) | (x >> (32 - amount))
	}

	function method {:opauqe} BitSignExtend(x:bv32, sz:int): bv32
		requires 0 < sz < 32;
	{
		(x ^ (1 << (sz - 1))) - (1 << (sz - 1))
	}
			
	function method BoolToInt(b: bool) : int
	{
		if b then 1 else 0
	}

	////////////////////////
	// Operations on words
	////////////////////////

	function BitwiseAnd(x:uint32, y:uint32) : uint32
	{
		BitsToWord(BitAnd(WordToBits(x), WordToBits(y)))
	}

	function BitwiseOr(x:uint32, y:uint32):uint32
	{
		BitsToWord(BitOr(WordToBits(x), WordToBits(y)))
	}

	function BitwiseNot(x:uint32) : uint32
	{
		BitsToWord(BitNot(WordToBits(x)))
	}

	function BitwiseXor(x:uint32, y:uint32) : uint32
	{
		BitsToWord(BitXor(WordToBits(x), WordToBits(y)))
	}

	function RotateRight(x:uint32, amount:uint32) : uint32
		requires amount < 32;
	{
		BitsToWord(BitRotateRight(WordToBits(x), amount))
	}

	function RotateLeft(x:uint32, amount:uint32):uint32
		requires amount < 32;
	{
		BitsToWord(BitRotateLeft(WordToBits(x), amount))
	}

	function RightShift(x:uint32, amount:uint32) : uint32
		requires amount < 32;
	{
		BitsToWord(BitShiftRight(WordToBits(x), amount))
	}

	function LeftShift(x:uint32, amount:uint32) : uint32
		requires amount < 32;
	{
		BitsToWord(BitShiftLeft(WordToBits(x), amount))
	}

	function {:opaque} BitwiseAdd32(x:uint32, y:uint32):uint32
	{
		(x + y) % 0x1_0000_0000
	}

	function {:opaque} BitwiseAddCarry(x:uint32, y:uint32):uint64
	{
		(x + y) % 0x1_0000_0000_0000_0000
	}

	function BitwiseSub32(x:uint32, y:uint32):uint32
	{
		BitsToWord(BitSub(WordToBits(x), WordToBits(y)))
	}

	function BitwiseMul32(x:uint32, y:uint32):uint32
	{
		BitsToWord(BitMul(WordToBits(x), WordToBits(y)))
	}

	function BitwiseDiv32(x:uint32, y:uint32):uint32
		requires y != 0;
	{
		if WordToBits(y) == 0 then 0 else BitsToWord(BitDiv(WordToBits(x), WordToBits(y)))
	}

	function BitwiseMod32(x:uint32, y:uint32):uint32
		requires y != 0;
	{
		if WordToBits(y) == 0 then 0 else BitsToWord(BitMod(WordToBits(x), WordToBits(y)))
	}

	function BitwiseSignExtend(x:uint32, size:int):uint32
		requires 0 <= size < 32;
	{
		if size == 0 then x else BitsToWord(BitSignExtend(WordToBits(x), size))
	}

	////////////////////////
	// Operations on bv256s
	////////////////////////

	function {:opaque} uint256_xor(x: uint256, y: uint256): uint256
	{
		(x as bv256 ^ y as bv256) as uint256
	}

	function {:opaque} uint256_or(x: uint256, y: uint256): uint256
	{
		(x as bv256 | y as bv256) as uint256
	}
	
	function {:opaque} uint256_and(x: uint256, y: uint256): uint256
	{
		(x as bv256 | y as bv256) as uint256
	}

	function {:opaque} uint256_ls(x: uint256, num_bytes:int): (r: uint256)
		requires 0 <= num_bytes < 32;
		ensures (num_bytes == 0) ==> r == x;
		ensures (num_bytes == 8) ==> r == x * BASE_64;
	{
		assume false;
		(x as bv256 << (num_bytes * 8)) as uint256
	}

	function {:opaque} uint256_rs(x:uint256, num_bytes:int): uint256
		requires 0 <= num_bytes < 32;
		ensures uint256_rs(x, 0) == x;
	{
		assume false;
		(x as bv256 >> (num_bytes * 8)) as uint256
	}

	function uint256_sb(b:uint256, st:bool, sb:uint32) : uint256
		requires sb < 32;
	{	
		if sb == 0 then b
		else if st then uint256_ls(b, sb)
		else uint256_rs(b, sb)
	}

	function {:opaque} uint256_lh(x: uint256): uint128
	{
		x % BASE_128
	}

	function {:opaque} uint256_uh(x: uint256): uint128
	{
		x / BASE_128
	}

	function {:opaque} uint256_hwb(x: uint256, v: uint128, lower: bool): (x': uint256)
		// overwrites the lower half, keeps the higher half
		ensures lower ==> (uint256_lh(x') == v && uint256_uh(x') == uint256_uh(x));
		// overwrites the higher half, keeps the lower half
		ensures !lower ==> (uint256_uh(x') == v && uint256_lh(x') == uint256_lh(x));

	function {:opaque} uint256_qmul(x: uint256, qx: uint2, y: uint256, qy:uint2): uint128
	{
		assume false; // TODO: add a bound proof
		uint256_qsel(x, qx) * uint256_qsel(y, qy)
	}

	function {:opaque} uint256_qsel(x: uint256, qx: uint2): uint64
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

	// lemma lemma_ls_mul(x: uint256)
	// 	requires x < BASE_128;
	// 	ensures uint256_ls(x, 8) == x * BASE_64;

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
