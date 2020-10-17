include "../spec/types.dfy"
include "../spec/ops.dfy"
include "../spec/def.dfy"
include "vale.dfy"
include "../gen/decls.dfy"
include "../lib/powers.dfy"
include "../lib/congruences.dfy"

module otbn_mul_lemmas {
	import opened types
	import opened ops
	import opened bignum_vale
	import opened bignum_def
	import opened bignum_decls
	import opened congruences
	import opened powers

	predicate half_product(w1: uint256, w28: uint256, w29: uint256)
	{
		w1 == (w28 * w29) % BASE_256
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
        wacc: uint256,
		w1_g1: uint256,
		w1_g2: uint256,
		result_g1: uint256,
		result_g2: uint256,
		w1: uint256,
		w28: uint256,
		w29: uint256
	)
		requires pc1: wacc_g1 == mulqacc256(true, w28, 0, w29, 0, 0, 0);
		requires pc2: wacc_g2 == mulqacc256(false, w28, 1, w29, 0, 1, wacc_g1);
		requires pc3: result_g1 == mulqacc256(false, w28, 0, w29, 1, 1, wacc_g2)
			&& wacc_g3 == uint256_uh(result_g1)
			&& w1_g2 == uint256_hwb(w1_g1, uint256_lh(result_g1), true);
		requires pc4: wacc_g4 == mulqacc256(false, w28, 2, w29, 0, 0, wacc_g3);
		requires pc5: wacc_g5 == mulqacc256(false, w28, 1, w29, 1, 0, wacc_g4);
		requires pc6: wacc_g6 == mulqacc256(false, w28, 0, w29, 2, 0, wacc_g5);
		requires pc7: wacc_g7 == mulqacc256(false, w28, 3, w29, 0, 1, wacc_g6);
		requires pc8: wacc_g8 == mulqacc256(false, w28, 2, w29, 1, 1, wacc_g7);
		requires pc9: wacc_g9 == mulqacc256(false, w28, 1, w29, 2, 1, wacc_g8);
		requires pc10: result_g2 == mulqacc256(false, w28, 0, w29, 3, 1, wacc_g9)
			&& wacc == uint256_uh(result_g2)
			&& w1 == uint256_hwb(w1_g2, uint256_lh(result_g2), false);
		ensures half_product(w1, w28, w29);
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
		}

		assert wacc_g2 == wacc_g1 + p2 * BASE_64 by {
			reveal pc2;
		}

		assert result_g1 == wacc_g2 + p3 * BASE_64
			&& wacc_g3 == uint256_uh(result_g1) 
			&& w1_g2 == uint256_hwb(w1_g1, uint256_lh(result_g1), true)
		by {
			reveal pc3;
			assert result_g1 == wacc_g2 + p3 * BASE_64;
		}

		assert wacc_g4 == wacc_g3 + p4 by {
			reveal pc4;
		}

		assert wacc_g5 == wacc_g4 + p5 by {
			reveal pc5;
		}

		assert wacc_g6 == wacc_g5 + p6 by {
			reveal pc6;
		}

		assert wacc_g7 == wacc_g6 + p7 * BASE_64 by {
			reveal pc7;
		}

		assert wacc_g8 == wacc_g7 + p8 * BASE_64 by {
			reveal pc8;
		}

		assert wacc_g9 == wacc_g8 + p9 * BASE_64 by {
			reveal pc9;
		}

		assert result_g2 == wacc_g9 + p10 * BASE_64
			&& w1 == uint256_hwb(w1_g2, uint256_lh(wacc_g9 + p10 * BASE_64), false) by {
			reveal pc10;
			assert result_g2 == wacc_g9 + p10 * BASE_64;
		}

		var lo := uint256_lh(result_g1);
		var hi := uint256_lh(result_g2);

		calc == {
			w1;
			w1 % BASE_256;
			{
				assert w1 == lo + hi * BASE_128 by {
					lemma_uint256_hwb(w1_g1, w1_g2, w1, lo, hi);
				}
			}
			(lo + hi * BASE_128) % BASE_256;
			{
				calc == {
					(lo + result_g2 * BASE_128) % BASE_256;
					{
						lemma_uint256_half_split(result_g2);
					}
					(lo + uint256_lh(result_g2) * BASE_128 + uint256_uh(result_g2) * BASE_256) % BASE_256;
					{
						lemma_mod_multiple_cancel(lo + uint256_lh(result_g2) * BASE_128, uint256_uh(result_g2) * BASE_256, BASE_256);
					}
					(lo + uint256_lh(result_g2) * BASE_128) % BASE_256;
					(lo + hi * BASE_128) % BASE_256;
				}
			}
			(lo + result_g2 * BASE_128) % BASE_256;
			{
				calc == {
					lo + result_g2 * BASE_128;
					lo + wacc_g9 * BASE_128 + p10 * BASE_192;
					{
						assert wacc_g9 == 
							uint256_uh(result_g1) + p4 + p5 + p6 + p7 * BASE_64 + p8 * BASE_64 + p9 * BASE_64;
					}
					lo + uint256_uh(result_g1) * BASE_128 +
						p4 * BASE_128 + p5 * BASE_128 + p6 * BASE_128 + p7 * BASE_192 + p8 * BASE_192 + p9 * BASE_192 + p10 * BASE_192;
					{
						lemma_uint256_half_split(result_g1);
					}
					result_g1 + p4 * BASE_128 + p5 * BASE_128 + p6 * BASE_128 + p7 * BASE_192 + p8 * BASE_192 + p9 * BASE_192 + p10 * BASE_192;
					{
						assert result_g1 == p1 + p2 * BASE_64 + p3 * BASE_64;
					}
					p1 + p2 * BASE_64 + p3 * BASE_64 + p4 * BASE_128 + p5 * BASE_128 + p6 * BASE_128 + p7 * BASE_192 + p8 * BASE_192 + p9 * BASE_192 + p10 * BASE_192;
				}
			}
			(p1 + p2 * BASE_64 + p3 * BASE_64 + p4 * BASE_128 + p5 * BASE_128 + p6 * BASE_128 + p7 * BASE_192 + p8 * BASE_192 + p9 * BASE_192 + p10 * BASE_192) % BASE_256;
			{
				lemma_quater_half_mul(w28, w29);
			}
			(w28 * w29) % BASE_256;
		}
		assert w1 == (w28 * w29) % BASE_256;
	}

	lemma lemma_quater_half_mul(x: uint256, y: uint256)
		ensures (x * y) % BASE_256 == 
			(uint256_qmul(x, 0, y, 0) +
			uint256_qmul(x, 1, y, 0) * BASE_64 + uint256_qmul(x, 0, y, 1) * BASE_64 +
			uint256_qmul(x, 2, y, 0) * BASE_128 + uint256_qmul(x, 1, y, 1) * BASE_128 + uint256_qmul(x, 0, y, 2) * BASE_128 +
			uint256_qmul(x, 3, y, 0) * BASE_192 + uint256_qmul(x, 2, y, 1) * BASE_192 + uint256_qmul(x, 1, y, 2) * BASE_192 + uint256_qmul(x, 0, y, 3) * BASE_192) % BASE_256;
	{
		var left := uint256_qmul(x, 0, y, 0) +
			uint256_qmul(x, 1, y, 0) * BASE_64 + uint256_qmul(x, 0, y, 1) * BASE_64 +
			uint256_qmul(x, 2, y, 0) * BASE_128 + uint256_qmul(x, 1, y, 1) * BASE_128 + uint256_qmul(x, 0, y, 2) * BASE_128 +
			uint256_qmul(x, 3, y, 0) * BASE_192 + uint256_qmul(x, 2, y, 1) * BASE_192 + uint256_qmul(x, 1, y, 2) * BASE_192 + uint256_qmul(x, 0, y, 3) * BASE_192;
			
		var right := uint256_qmul(x, 3, y, 1) * BASE_256 + uint256_qmul(x, 2, y, 2) * BASE_256 + uint256_qmul(x, 1, y, 3) * BASE_256 + 
			uint256_qmul(x, 3, y, 2) * BASE_256 * BASE_64 + uint256_qmul(x, 2, y, 3) * BASE_256 * BASE_64 + 
			uint256_qmul(x, 3, y, 3) * BASE_256 * BASE_128;

		assert x * y == left + right by {
			lemma_quater_full_mul(x, y);
		}

		assert (x * y) % BASE_256 == left % BASE_256 by {
			lemma_mod_multiple_cancel(left, right, BASE_256);
		}
	}

	lemma lemma_quater_full_mul(x: uint256, y: uint256)
		ensures x * y ==
			uint256_qmul(x, 0, y, 0) +
			uint256_qmul(x, 1, y, 0) * BASE_64 + uint256_qmul(x, 0, y, 1) * BASE_64 +
			uint256_qmul(x, 2, y, 0) * BASE_128 + uint256_qmul(x, 1, y, 1) * BASE_128 + uint256_qmul(x, 0, y, 2) * BASE_128 +
			uint256_qmul(x, 3, y, 0) * BASE_192 + uint256_qmul(x, 2, y, 1) * BASE_192 + uint256_qmul(x, 1, y, 2) * BASE_192 + uint256_qmul(x, 0, y, 3) * BASE_192 +
			uint256_qmul(x, 3, y, 1) * BASE_256 + uint256_qmul(x, 2, y, 2) * BASE_256 + uint256_qmul(x, 1, y, 3) * BASE_256 + 
			uint256_qmul(x, 3, y, 2) * BASE_256 * BASE_64 + uint256_qmul(x, 2, y, 3) * BASE_256 * BASE_64 + 
			uint256_qmul(x, 3, y, 3) * BASE_256 * BASE_128;
	{
		var a0 := uint256_qsel(x, 0);
		var a1 := uint256_qsel(x, 1);
		var a2 := uint256_qsel(x, 2);
		var a3 := uint256_qsel(x, 3);

		var b0 := uint256_qsel(y, 0);
		var b1 := uint256_qsel(y, 1);
		var b2 := uint256_qsel(y, 2);
		var b3 := uint256_qsel(y, 3);

		assert x == a0 + a1 * BASE_64 + a2 * BASE_128 + a3 * BASE_192 by {
			lemma_uint256_quarter_split(x);
		}

		assert y == b0 + b1 * BASE_64 + b2 * BASE_128 + b3 * BASE_192 by {
			lemma_uint256_quarter_split(y);
		}

		assert x * y == uint256_qmul(x, 0, y, 0) +
			uint256_qmul(x, 1, y, 0) * BASE_64 + uint256_qmul(x, 0, y, 1) * BASE_64 +
			uint256_qmul(x, 2, y, 0) * BASE_128 + uint256_qmul(x, 1, y, 1) * BASE_128 + uint256_qmul(x, 0, y, 2) * BASE_128 +
			uint256_qmul(x, 3, y, 0) * BASE_192 + uint256_qmul(x, 2, y, 1) * BASE_192 + uint256_qmul(x, 1, y, 2) * BASE_192 + uint256_qmul(x, 0, y, 3) * BASE_192 +
			uint256_qmul(x, 3, y, 1) * BASE_256 + uint256_qmul(x, 2, y, 2) * BASE_256 + uint256_qmul(x, 1, y, 3) * BASE_256 + 
			uint256_qmul(x, 3, y, 2) * BASE_256 * BASE_64 + uint256_qmul(x, 2, y, 3) * BASE_256 * BASE_64 + 
			uint256_qmul(x, 3, y, 3) * BASE_256 * BASE_128
		by {
			reveal uint256_qmul();
		}
	}

    lemma lemma_mod_multiple_cancel(x: int, y: int, m: nat)
		requires m !=0 && y % m == 0;
		ensures (x + y) % m == x % m;
}