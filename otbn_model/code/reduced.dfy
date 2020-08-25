module example_lemmas {
	type uint32  = i:int | 0 <= i < 0x1_0000_0000
	type uint256 = i:int | 0 <= i < 0x1_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000
	type Bignum = uint256

	function BignumXor(a:Bignum, b:Bignum, st:bool, sb:uint32) : Bignum
		requires sb < 32;
	{
		BitsToBignum(bv256_xor(BignumToBits(a), BignumToBits(BignumShift(b, false, 0))))
	}

	function BignumShift(b:Bignum, st:bool, sb:uint32) : Bignum
		requires sb < 32;
	{
		if st == false then RightShift256(b, sb) else LeftShift256(b, sb)
	}

	function RightShift256(x:Bignum, amount:uint32) : Bignum
		requires amount < 32;
	{
		BitsToBignum(bv256_lshift(BignumToBits(x), amount))
	}

	function LeftShift256(x:uint256, amount:uint32) : Bignum
		requires amount < 32;
	{
		BitsToBignum(bv256_rshift(BignumToBits(x), amount))
	}

	function method {:opaque} bv256_lshift(x:bv256, num_bytes:int): bv256
		requires 0 <= num_bytes < 32;
	{
		x << num_bytes * 8
	}

	function method {:opaque} bv256_xor(a: bv256, b: bv256) : bv256 {
		a ^ b
	}

	function method {:opaque} bv256_rshift(x:bv256, num_bytes:int): bv256
		requires 0 <= num_bytes < 32;
	{
		x >> num_bytes * 8
	}

	function method {:opaque} BitsToBignum(b:bv256) : uint256 { b as uint256 }
	// function method BitsToBignum(b:bv256) : uint256 { b as uint256 }

	function method {:opaque} BignumToBits(bn:uint256) : bv256 { bn as bv256 }
	// function method BignumToBits(bn:uint256) : bv256 { bn as bv256 }

	lemma lemma_xor_clear(x: uint256, y: uint256)
		requires x == y;
	    // ensures xor256(x, y, false, 0) == 0;
	{
		calc == {
			BignumXor(x, y, false, 0);
			BitsToBignum(bv256_xor(BignumToBits(x), BignumToBits(BignumShift(y, false, 0))));
			BitsToBignum(bv256_xor(BignumToBits(x), BignumToBits(RightShift256(y, 0))));
			BitsToBignum(bv256_xor(BignumToBits(x), BignumToBits(BitsToBignum(bv256_lshift(BignumToBits(y), 0)))));
			{
				assume bv256_lshift(BignumToBits(y), 0) == BignumToBits(y);
			}
			BitsToBignum(bv256_xor(BignumToBits(x), BignumToBits(BitsToBignum(BignumToBits(y)))));
			{
				assume BitsToBignum(BignumToBits(y)) == y;
			}
			BitsToBignum(bv256_xor(BignumToBits(x), BignumToBits(y)));
			{
				assume bv256_xor(BignumToBits(x), BignumToBits(x)) == 0;
			}
			BitsToBignum(0);
			{
				reveal BitsToBignum();
			}
			0;
		}

		// assume false;
	}
}