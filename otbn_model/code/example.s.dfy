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
			uint256_xor(x, uint256_rs(x, 0));
			{
				reveal uint256_rs();
				assume uint256_rs(x, 0) == x;
			}
			uint256_xor(x, x);
			{
				reveal uint256_xor();
			}
			0;
		}
	}
}