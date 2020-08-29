include "../spec/types.dfy"
include "../spec/ops.dfy"
include "../spec/def.dfy"
include "vale.dfy"
include "../gen/decls.dfy"

module example_lemmas {
	import opened types
	import opened ops
	import opened bignum_vale
	import opened bignum_def
	import opened bignum_decls

	lemma lemma_xor_clear(x: uint256)
	    ensures xor256(x, x, false, 0) == 0;
	{
		reveal uint256_xor();
	}

	lemma lemma_sb_nop(x: uint256)
		ensures uint256_ls(x, 0) == x;
		ensures uint256_rs(x, 0) == x;
	{
		assume false;
		reveal uint256_ls();
		reveal uint256_rs();
	}
}