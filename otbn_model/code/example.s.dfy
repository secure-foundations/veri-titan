include "../spec/types.dfy"
include "../spec/ops.dfy"
include "../spec/def.dfy"
include "vale.dfy"
include "decls.dfy"

module example_lemmas {
	import opened types
	import opened ops
	import opened bignum_vale
	import opened bignum_def
	import opened bignum_decls

	lemma lemma_xor_clear(x: uint256)
	    ensures xor256(x, x, false, 0) == 0;
	{
		calc == {
			xor256(x, x, false, 0);
			BignumXor(x, x, false, 0);
			{
				assume false; // why does this calc not hold?
			}
		    BitsToBignum(BignumToBits(x) ^ BignumToBits(BignumShift(x, false, 0)));
			{
				reveal BignumToBits();
			}
			BitsToBignum(x as bv256 ^ BignumShift(x, false, 0) as bv256);
		}

		// reveal BignumToBits();
		// reveal BitShiftRight256();
		assume false;
		// assert x as bv256 ^ x as bv256 == 0;
	}
}