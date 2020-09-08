include "../spec/types.dfy"
include "../spec/ops.dfy"
include "../spec/def.dfy"
include "vale.dfy"
include "../gen/decls.dfy"
include "../../dfy_model/powers.dfy"
include "../../dfy_model/congruences.dfy"

module example_lemmas {
	import opened types
	import opened ops
	import opened bignum_vale
	import opened bignum_def
	import opened bignum_decls
	import opened congruences
	import opened powers

	function half_product(w1: uint256, w28: uint256, w29: uint256): bool
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
			// lemma_sb_nop(p1);
		}

		assert wacc_g2 == wacc_g1 + p2 * BASE_64 by {
			reveal pc2;
			lemma_ls_mul(p2);
		}

		assert result_g1 == wacc_g2 + p3 * BASE_64
			&& wacc_g3 == uint256_uh(result_g1) 
			&& w1_g2 == uint256_hwb(w1_g1, uint256_lh(result_g1), true)
		by {
			reveal pc3;
			assert result_g1 == wacc_g2 + p3 * BASE_64 by {
				lemma_ls_mul(p3);
			}
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
			lemma_ls_mul(p7);
		}

		assert wacc_g8 == wacc_g7 + p8 * BASE_64 by {
			reveal pc8;
			lemma_ls_mul(p8);
		}

		assert wacc_g9 == wacc_g8 + p9 * BASE_64 by {
			reveal pc9;
			lemma_ls_mul(p9);
		}

		assert result_g2 == wacc_g9 + p10 * BASE_64
			&& w1 == uint256_hwb(w1_g2, uint256_lh(wacc_g9 + p10 * BASE_64), false) by {
			reveal pc10;
			assert result_g2 == wacc_g9 + p10 * BASE_64 by {
				lemma_ls_mul(p10);
			}
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

	lemma lemma_d0inv_pre_loop(w0_g1: uint256, w0_g2: uint256, w0: uint256, w29: uint256)
		requires w0_g2 == xor256(w0_g1, w0_g1, false, 0);
		requires w0 == fst(addi256(w0_g2, 1));
		requires w29 == w0;
		ensures w0 == power(2, 0) && w29 == 1;
	{
		assert w0_g2 == 0 by {
			lemma_xor_clear(w0_g1);
		}

		assert w0 == 1;
		assert w29 == 1;

		assert w0 == power(2, 0) by {
			reveal power();
		}
	}

	predicate invariant_d0inv(i: uint32, w28: uint256, w29: uint256, w0: uint256)
	{
		&& (0 <= i <= 256)
		&& ((i == 0) ==> (w29 == 1))
        && ((i > 0) ==> ((w29 * w28) % power(2, i) == 1))
		&& ((i > 0) ==> (w29 < power(2, i)))
        && ((i < 256) ==> (w0 == power(2, i)))
	}

	lemma lemma_d0inv_mid_loop(
		i: uint32,
		w0: uint256,
		w0_g1: uint256,
		w1_g1: uint256,
		w1_g2: uint256,
		w28: uint256,
		w29: uint256,
		w29_g1: uint256
	)
        requires w28 % 2 == 1;
        requires invariant_d0inv(i, w28, w29_g1, w0_g1);
		requires i < 256;
        requires half_product(w1_g1, w28, w29_g1);
        requires w1_g2 == and256(w1_g1, w0_g1, false, 0);
        requires w29 == or256(w29_g1, w1_g2, false, 0);
        requires w0 == fst(add256(w0_g1, w0_g1, false, 0));

		ensures invariant_d0inv(i + 1, w28, w29, w0);
	{
		if i == 0 {
			assert w1_g1 == (w28 * w29_g1) % BASE_256;
			assert w0_g1 == 1 by {
				reveal power();
			}
			odd_and_one_lemma(w1_g1);
			// assert w1_g2 == uint256_and(w1_g1, w0_g1);
			assert w29 == uint256_or(1, 1);
			assert w29 == 1 by {
				reveal uint256_or();
			}
			assert w0 == power(2, i + 1) by {
				reveal power();
			}
		} else {
            assume w0 == if i != 255 then power(2, i + 1) else 0;

			and_single_bit_lemma(w1_g2, w1_g1, w0_g1, i);
			if w1_g2 == 0 {
				or_zero_nop_lemma(w29_g1, w1_g2);
				d0inv_bv_lemma_1(w28 * w29, w0_g1, i);
				assert w29 < power(2, i + 1) by {
					reveal power();
				}
			} else {
				or_single_bit_add_lemma(w29, w29_g1, w0_g1, i);
				d0inv_bv_lemma_2(w28 * w29_g1, w28, w0_g1, i);
			}
		}
	}

	lemma lemma_d0inv_post_loop(
		w28: uint256,
		w29: uint256,
		w29_g2: uint256,
		w31: uint256
	)
		requires w31 == 0;
		requires w29 == fst(sub256(w31, w29_g2, false, 0));
		requires (w29_g2 * w28) % power(2, 256) == 1;
		ensures cong(w29 * w28, -1, BASE_256);
	{
		assume BASE_256 == power(2, 256);
		assert w29 == (w31 - w29_g2) % BASE_256;
		mod_inv_lemma(w29, w29_g2, w28);
	}

    lemma mod_inv_lemma(w29: int, w29_old: int, w28: int)
        requires (w29_old * w28) % BASE_256 == 1;
        requires w29_old + w29 == BASE_256;
        ensures cong(w29 * w28, -1, BASE_256);
    {
        calc ==> {
            (w29_old * w28) % BASE_256 == 1;
            {
                reveal cong();
            }
            cong(w29_old * w28, 1, BASE_256);
            {
                assert w29_old == BASE_256 - w29;
            }
            cong((BASE_256 - w29) * w28, 1, BASE_256);
            cong(BASE_256 * w28 - w29 * w28, 1, BASE_256);
            {
                assert cong(-BASE_256 * w28, 0, BASE_256) by {
                    mod_mul_lemma(w28, -BASE_256, BASE_256);
                    reveal cong();
                }
                cong_add_lemma_2(BASE_256 * w28 - w29 * w28, 1, -BASE_256 * w28, 0, BASE_256);
            }
            cong(-w29 * w28, 1, BASE_256);
            {
                cong_mul_lemma_1(-w29 * w28, 1, -1, BASE_256);
            }
            cong(w29 * w28, -1, BASE_256);
        }
    }

    lemma power_2_bounded_lemma(i: int)
        requires 0 <= i < 256;
        ensures power(2, i) < BASE_256;

    lemma {:axiom} d0inv_bv_lemma_1(x: int, w0: uint256, i: nat)
        requires w0 == power(2, i);
        requires x % w0 == 1;
        requires uint256_and(x % BASE_256, w0) == 0;
        ensures x % power(2, i + 1) == 1;

    lemma {:axiom} d0inv_bv_lemma_2(x: int, w28: uint256, w0: uint256, i: nat)
        requires w0 == power(2, i);
        requires x % w0 == 1;
        requires uint256_and(x % BASE_256, w0) == w0;
        requires w28 % 2 == 1;
        ensures (x + w28 * w0) % power(2, i + 1) == 1;

	lemma lemma_mod_multiple_cancel(x: int, y: int, m: nat)
		requires m !=0 && y % m == 0;
		ensures (x + y) % m == x % m;

	// bv lemmas/axioms

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
	    ensures xor256(x, x, false, 0) == 0;
	{
		reveal uint256_xor();
	}

	// lemma lemma_sb_nop(x: uint256)
	// 	ensures uint256_ls(x, 0) == x;
	// 	ensures uint256_rs(x, 0) == x;

	lemma lemma_ls_mul(x: uint256)
		requires x < BASE_128;
		ensures uint256_ls(x, 8) == x * BASE_64;

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
}