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

	lemma lemma_ls_mul(x: uint256)
		requires x < HALF_BASE;
		ensures uint256_ls(x, 8) == x * QUARTER_BASE;

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

    requires pc1: wacc_g1 == mulqacc256(true, w28, 0, w29, 0, 0, 0);
    requires pc2: wacc_g2 == mulqacc256(false, w28, 1, w29, 0, 1, wacc_g1);
    requires pc3: result_g1 == mulqacc256(false, w28, 1, w29, 0, 1, wacc_g2)
		&& wacc_g3 == uint256_uh(result_g1)
        && w1_g1 == uint256_hwb(0, uint256_lh(result_g1), true);
    requires pc4: wacc_g4 == mulqacc256(false, w28, 2, w29, 0, 0, wacc_g3);
    requires pc5: wacc_g5 == mulqacc256(false, w28, 1, w29, 1, 0, wacc_g4);
    requires pc6: wacc_g6 == mulqacc256(false, w28, 0, w29, 2, 0, wacc_g5);
    requires pc7: wacc_g7 == mulqacc256(false, w28, 3, w29, 0, 1, wacc_g6);
    requires pc8: wacc_g8 == mulqacc256(false, w28, 2, w29, 1, 1, wacc_g7);
    requires pc9: wacc_g9 == mulqacc256(false, w28, 1, w29, 2, 1, wacc_g8);
    requires pc10: result_g2 == mulqacc256(false, w28, 0, w29, 3, 1, wacc_g9)
		&& w1 == uint256_hwb(w1_g1, uint256_lh(result_g2), false);
	{
		var p1 := uint256_qmul(w28, 0, w29, 0);
		var p2 := uint256_qmul(w28, 1, w29, 0);
		var p3 := uint256_qmul(w28, 0, w29, 1);
		var p4 := uint256_qmul(w28, 2, w29, 0);
		var p5 := uint256_qmul(w28, 1, w29, 1);
		var p6 := uint256_qmul(w28, 0, w29, 2);
		var p7 := uint256_qmul(w28, 3, w29, 0);
		var p8 := uint256_qmul(w28, 2, w29, 1);
		var p9 := uint256_qmul(w28, 1, w29, 2);
		var p10 := uint256_qmul(w28, 0, w29, 3);

		assert wacc_g1 == p1 by {
			reveal pc1;
			lemma_sb_nop(p1);
		}

		assert wacc_g2 == mulqacc256(false, w28, 1, w29, 0, 1, wacc_g1) by {
			var shift := uint256_ls(p2, 8);

			calc == {
				wacc_g2;
				{
					reveal pc2;
				}
				mulqacc256(false, w28, 1, w29, 0, 1, wacc_g1);
				(wacc_g1 + shift) % BASE;
				{
					lemma_ls_mul(p2);
					assert shift == p2 * QUARTER_BASE;
				}
				(wacc_g1 + p2 * QUARTER_BASE) % BASE;
			}
			assume false;
		}
	}

}