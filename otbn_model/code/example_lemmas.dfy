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

	lemma lemma_bn_half_mul(
		wacc_g1: uint256,
		wacc_g2: uint256,
		wacc_g3: uint256,
		wacc_g4: uint256,
		wacc_g5: uint256,
		wacc_g6: uint256,
		wacc_g7: uint256,
		wacc_g8: uint256,
		wacc_g9: uint256,
		w1_g1: uint256,
		result_g1: uint256,
		result_g2: uint256,
		w1: uint256,
		w28: uint256,
		w29: uint256
	)

    requires wacc_g1 == mulqacc256(true, w28, 0, w29, 0, 0, 0);
    requires wacc_g2 == mulqacc256(false, w28, 1, w29, 0, 1, wacc_g1);
    requires wacc_g3 == uint256_uh(result_g1)
        && w1_g1 == uint256_hwb(0, uint256_lh(result_g1), true);
    requires wacc_g4 == mulqacc256(false, w28, 2, w29, 0, 0, wacc_g3);
    requires wacc_g5 == mulqacc256(false, w28, 1, w29, 1, 0, wacc_g4);
    requires wacc_g6 == mulqacc256(false, w28, 0, w29, 2, 0, wacc_g5);
    requires wacc_g7 == mulqacc256(false, w28, 3, w29, 0, 1, wacc_g6);
    requires wacc_g8 == mulqacc256(false, w28, 2, w29, 1, 1, wacc_g7);
    requires wacc_g9 == mulqacc256(false, w28, 1, w29, 2, 1, wacc_g8);
    requires w1 == uint256_hwb(w1_g1, uint256_lh(result_g2), false);




}