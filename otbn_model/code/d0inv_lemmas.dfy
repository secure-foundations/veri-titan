include "../spec/types.dfy"
include "../spec/ops.dfy"
include "../spec/def.dfy"
include "vale.dfy"
include "../gen/decls.dfy"
include "../lib/powers.dfy"
include "../lib/congruences.dfy"
include "otbn_mul_lemmas.dfy"

module d0inv_lemmas {
	import opened types
	import opened ops
	import opened bignum_vale
	import opened bignum_def
	import opened bignum_decls
	import opened congruences
	import opened powers
    import opened otbn_mul_lemmas

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

		assert w0 == if i != 255 then power(2, i + 1) else 0 by {
				calc == {
					w0;
					(w0_g1 + w0_g1) % BASE_256;
					(w0_g1 * 2) % BASE_256;
					{
						assert w0_g1 == power(2, i);
					}
					(power(2, i) * 2) % BASE_256;
					{
						power_add_one_lemma(2, i);
					}
					power(2, i + 1) % BASE_256;
					{
						power_2_bounded_lemma(i + 1);
					}
					if i != 255 then power(2, i + 1) else 0;
				}
			}

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

	predicate d0inv_256(w29: uint256, w28: uint256)
	{
		cong(w29 * w28, -1, BASE_256)
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
		ensures d0inv_256(w29, w28);
	{
		power_2_bounded_lemma(256);
		assert w29 == (w31 - w29_g2) % BASE_256;
        assume false;
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
		ensures (0 <= i < 256) ==> (power(2, i) < BASE_256);
		ensures (i == 256) ==> (power(2, i) == BASE_256);
		// ensures (i > 256) ==> (power(2, i) > BASE_256);

	lemma {:axiom} d0inv_bv_lemma_1(x: int, w0: uint256, i: nat)
		requires i < 256;
		requires w0 == power(2, i);
		requires x % w0 == 1;
		requires uint256_and(x % BASE_256, w0) == 0;
		ensures x % power(2, i + 1) == 1;

	lemma {:axiom} d0inv_bv_lemma_2(x: int, w28: uint256, w0: uint256, i: nat)
		requires i < 256;
		requires w0 == power(2, i);
		requires x % w0 == 1;
		requires uint256_and(x % BASE_256, w0) == w0;
		requires w28 % 2 == 1;
		ensures (x + w28 * w0) % power(2, i + 1) == 1;
}