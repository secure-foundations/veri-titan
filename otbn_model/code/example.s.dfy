include "../spec/types.dfy"
include "vale.dfy"
include "../spec/def.dfy"
include "decls.dfy"
include "example.s.dfy"

module example_lemmas {
	import opened types
	import opened bignum_vale
	import opened bignum_def
	import opened bignum_decls

	lemma lemma_nonsense(x: uint256)
	    ensures xor256(x, x, false, 0) == 0;
	{
	    assume false;
	}
}