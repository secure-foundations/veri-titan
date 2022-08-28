// include "mq_polys.dfy"
include "poly_view.i.dfy"

module ntt_twiddle_i(MQ: ntt_param_s) {
	import opened Power
	import opened Power2
	import opened DivMod
	import opened Mul

	import opened pow2_s
	import opened ntt_index

	import MQP = mq_poly_i(MQ)
	import PV = poly_view_i(MQ)

	type elem = MQ.elem
	type n_elems = MQ.n_elems

	const Q := MQ.Q;
	const R := MQ.R;
	const PSI := MQ.PSI;
	const OMEGA := MQ.OMEGA;
	const OMEGA_INV := MQ.OMEGA_INV;

	ghost const N := MQ.N; 

	lemma primitive_root_non_zero_lemma(i: nat)
		requires i < N.full * 2;
		ensures MQP.mqpow(PSI, i) != 0;
	{
		var PSI := PSI;
		if Pow(PSI, i) % Q == 0 {
			var j := N.full * 2 - i;
			calc == {
				1;
				{
					MQ.Nth_root_lemma();
				}
				Pow(PSI, i + j) % Q;
				{
					LemmaPowAdds(PSI, i, j);
				}
				(Pow(PSI, i) * Pow(PSI, j)) % Q;
				{
					LemmaMulModNoopGeneral(Pow(PSI, i), Pow(PSI, j), Q);
				}
				(Pow(PSI, i) % Q * (Pow(PSI, j) % Q)) % Q;
				(0 * (Pow(PSI, j) % Q)) % Q;
				(0) % Q;
				0;
			}
			assert false;
		}
	}

	lemma full_rotation_lemma(a: nat)
		ensures MQP.mqpow(PSI, a + 2 * N.full) == MQP.mqpow(PSI, a);
	{
		var PSI := PSI;
		var N := N.full;
		calc == {
			Pow(PSI, a + 2 * N) % Q;
			{
				LemmaPowAdds(PSI, a, 2 * N);
			}
			(Pow(PSI, a) * Pow(PSI, 2 * N)) % Q;
			{
				LemmaMulModNoopGeneral(Pow(PSI, a), Pow(PSI, 2 * N), Q);
			}
			((Pow(PSI, a) % Q) * (Pow(PSI, 2 * N) % Q)) % Q;
			{
				MQ.Nth_root_lemma();
				assert Pow(PSI, 2 * N) % Q == 1;
			}
			(Pow(PSI, a) % Q) % Q;
			{
				LemmaModBasicsAuto();
			}
			Pow(PSI, a) % Q;
		}
	}

	lemma inv_full_rotation_lemma(a: nat)
		ensures MQP.mqpow(OMEGA_INV, a + N.full) == MQP.mqpow(OMEGA_INV, a);
	{
		var N := N.full;
		MQ.Nth_root_lemma();

		calc == {
			1;
			{
				Lemma1Pow(N);
			}
			Pow(1, N) % Q;
			Pow(1 % Q, N) % Q;
			Pow((OMEGA * OMEGA_INV) % Q, N) % Q;
			{
				LemmaPowModNoop(OMEGA * OMEGA_INV, N, Q);
			}
			Pow(OMEGA * OMEGA_INV, N) % Q;
			{
				LemmaPowDistributes(OMEGA, OMEGA_INV, N);
			}
			(Pow(OMEGA, N) * Pow(OMEGA_INV, N)) % Q;
			{
				LemmaMulModNoopGeneral(Pow(OMEGA, N), Pow(OMEGA_INV, N), Q);
			}
			((Pow(OMEGA, N) % Q) * (Pow(OMEGA_INV, N) % Q)) % Q;
			((Pow(OMEGA_INV, N)) % Q) % Q;
			{
				LemmaModBasicsAuto();
			}
			Pow(OMEGA_INV, N) % Q;
		}

		calc == {
			Pow(OMEGA_INV, a + N) % Q;
			{
				LemmaPowAdds(OMEGA_INV, a, N);
			}
			(Pow(OMEGA_INV, a) * Pow(OMEGA_INV, N)) % Q;
			{
				LemmaMulModNoopGeneral(Pow(OMEGA_INV, a), Pow(OMEGA_INV, N), Q);
			}
			((Pow(OMEGA_INV, a) % Q) * (Pow(OMEGA_INV, N) % Q)) % Q;
			{
				assert Pow(OMEGA_INV, N) % Q == 1;
			}
			(Pow(OMEGA_INV, a) % Q) % Q;
			{
				LemmaModBasicsAuto();
			}
			Pow(OMEGA_INV, a) % Q;
		}
	}

	lemma half_rotation_lemma(a: nat)
		ensures Pow(PSI, a + N.full) % Q == (Q - Pow(PSI, a) % Q) % Q;
	{
		var PSI := PSI;
		var N := N.full;
		var t0 := Pow(PSI, a);
		calc == {
			Pow(PSI, a + N) % Q;
			{
				LemmaPowAdds(PSI, a, N);
			}
			(t0 * Pow(PSI, N)) % Q;
			{
				LemmaMulModNoopGeneral(t0, Pow(PSI, N), Q);
			}
			((t0 % Q) * (Pow(PSI, N) % Q)) % Q;
			{
				MQ.Nth_root_lemma();
				assert Pow(PSI, N) % Q == Q - 1;
			}
			((t0 % Q) * (Q - 1)) % Q;
			{
				LemmaMulModNoopGeneral(t0, Q - 1, Q);
			}
			(t0 * (Q - 1)) % Q;
			{
				LemmaMulIsDistributive(t0, Q, -1);
			}
			(t0 * Q - t0) % Q;
			{
				LemmaModMultiplesVanish(t0, -t0, Q);
			}
			(- t0) % Q;
			{
				LemmaModMultiplesVanish(1, -t0, Q);
			}
			(Q - t0) % Q;
			{
				LemmaSubModNoop(Q, t0, Q);
			}
			(Q - Pow(PSI, a) % Q) % Q;
		}
	}

	lemma inv_half_rotation_lemma(a: nat)
		ensures (N.full / 2) * 2 == N.full;
		ensures Pow(OMEGA_INV, a + N.full / 2) % Q == (Q - Pow(OMEGA_INV, a) % Q) % Q;
	{
		MQ.Nth_root_lemma();
		pow2_basics(N);
		var HN := N.full / 2;
		var t0 := Pow(OMEGA_INV, a);

		calc == {
			Pow(OMEGA_INV, a + HN) % Q;
			{
				LemmaPowAdds(OMEGA_INV, a, HN);
			}
			(t0 * Pow(OMEGA_INV, HN)) % Q;
			{
				LemmaMulModNoopGeneral(t0, Pow(OMEGA_INV, HN), Q);
			}
			((t0 % Q) * (Pow(OMEGA_INV, HN) % Q)) % Q;
			{
				MQ.Nth_root_lemma();
				assert Pow(OMEGA_INV, HN) % Q == Q - 1;
			}
			((t0 % Q) * (Q - 1)) % Q;
			{
				LemmaMulModNoopGeneral(t0, Q - 1, Q);
			}
			(t0 * (Q - 1)) % Q;
			{
				LemmaMulIsDistributiveAuto();
			}
			(t0 * Q - t0) % Q;
			{
				LemmaModMultiplesVanish(t0, -t0, Q);
			}
			(- t0) % Q;
			{
				LemmaModMultiplesVanish(1, -t0, Q);
			}
			(Q - t0) % Q;
			{
				LemmaSubModNoop(Q, t0, Q);
			}
			(Q - t0 % Q) % Q;
		}
	}

	lemma twiddle_factors_index_bound_lemma(t: pow2_t, j: nat)
		returns (d: pow2_t)
		requires t.exp < N.exp;
		requires j < t.full;
		ensures t.full + j < N.full;
		ensures d == pow2_half(PV.block_count(t));
		ensures 2 * j < PV.block_size(d).full;
	{
		assert t.full <= N.full / 2 by {
			reveal Pow2();
			LemmaPowIncreases(2, t.exp, N.exp-1);
			assert pow2(N.exp-1) == pow2_half(pow2(N.exp));
			assert pow2(N.exp-1).full == N.full / 2;
		}
		calc {
			t.full + j;
			<
			2 * t.full;
			<=
			2 * (N.full / 2);
			{
				pow2_basics(N);
			}
			N.full;
		}

		d := PV.block_count(t);
		assert PV.block_size(d) == t;

		calc {
			2 * j;
			<
			2 * t.full;
			2 * PV.block_size(d).full;
			pow2_double(PV.block_size(d)).full;
			{
				PV.block_count_half_lemma(d);
			}
			PV.block_size(pow2_half(d)).full;
		}

		d := pow2_half(PV.block_count(t));
	}

	// d is the block count
	// i is the offset in the block
	function rev_mixed_powers_mont_x_value_inner(i: nat, d: pow2_t): (r: elem)
		requires d.exp <= N.exp;
		requires i < PV.block_size(d).full;
		ensures r > 0;
	{
		var bound := PV.block_size(d);
		LemmaMulNonnegative(2 * bit_rev_int(i, bound), d.full);
		var r := MQP.mqpow(PSI, 2 * bit_rev_int(i, bound) * d.full + d.full);
		// LemmaPowPositive(PSI, 2 * bit_rev_int(i, bound) * d.full + d.full);
		calc {
			2 * bit_rev_int(i, bound) * d.full + d.full;
			{
				LemmaMulProperties();
			}
			(bit_rev_int(i, bound) * (2 * d.full)) + d.full;
			<=
			{
				LemmaMulInequality(bit_rev_int(i, bound), bound.full - 1, 2 * d.full);
			}
			(bound.full - 1) * (2 * d.full) + d.full;
			{
				LemmaMulIsDistributive(2 * d.full, bound.full, - 1);
			}
			bound.full * (2 * d.full) - (2 * d.full) + d.full;
			bound.full * (2 * d.full) - d.full;
			{
				LemmaMulProperties();
			}
			2 * (bound.full * d.full) - d.full;
			// {
			// 	PV.block_count_product_lemma(bound);
			// }
			2 * N.full - d.full;
		}
		primitive_root_non_zero_lemma(2 * bit_rev_int(i, bound) * d.full + d.full);
		r
	}

	function rev_mixed_powers_mont_x_value(i: nat, d: pow2_t): (r: elem)
	{
		if rev_mixed_powers_mont_x_value_inner.requires(i, d) then 
			rev_mixed_powers_mont_x_value_inner(i, d)
		else
			0
	}

	function method {:axiom} rev_mixed_powers_mont_table(): (t: seq<elem>)
		ensures |t| == N.full;

	lemma {:axiom} rev_mixed_powers_mont_table_axiom(t: pow2_t, d: pow2_t, j: nat)
		requires t.exp < N.exp;
		requires j < t.full;
		requires t.full + j < N.full;
		requires d == pow2_half(PV.block_count(t));
		requires 2 * j < PV.block_size(d).full;
		ensures rev_mixed_powers_mont_table()[t.full + j] ==
			MQP.mqmul(rev_mixed_powers_mont_x_value(2 * j, d), R);

	lemma rev_mixed_powers_mont_table_lemma(t: pow2_t, d: pow2_t, j: nat)
		requires t.exp < N.exp;
		requires j < t.full;
		requires d == pow2_half(PV.block_count(t));
		ensures t.full + j < N.full;
		ensures 2 * j < PV.block_size(d).full;
		ensures rev_mixed_powers_mont_table()[t.full + j] ==
			MQP.mqmul(rev_mixed_powers_mont_x_value(2 * j, d), R);
	{
		var _ := twiddle_factors_index_bound_lemma(t, j);
		rev_mixed_powers_mont_table_axiom(t, d, j);
	}

	// d is the block count
	// i is the offset in the block
	function rev_omega_inv_powers_x_value_inner(i: nat, d: pow2_t): (r: elem)
		requires d.exp <= N.exp;
		requires i < PV.block_size(d).full;
		ensures r > 0;
	{
		var bound := PV.block_size(d);
		LemmaMulNonnegative(bit_rev_int(i, bound), d.full);
		var r := MQP.mqpow(OMEGA_INV, bit_rev_int(i, bound) * d.full);
		assert r > 0 by {
			if r == 0 {
				var exp := bit_rev_int(i, bound) * d.full;

				calc == {
					1;
					{
						Lemma1Pow(exp);
					}
					Pow(1, exp) % Q;
					{
						MQ.Nth_root_lemma();
					}
					Pow((OMEGA_INV * OMEGA) % Q, exp) % Q;
					{
						LemmaPowModNoop(OMEGA_INV * OMEGA, exp, Q);
					}
					Pow(OMEGA_INV * OMEGA, exp) % Q;
					{
						LemmaPowDistributes(OMEGA_INV, OMEGA, exp);
					}
					(Pow(OMEGA_INV, exp) * Pow(OMEGA, exp)) % Q;
					{
						LemmaMulModNoop(Pow(OMEGA_INV, exp), Pow(OMEGA, exp), Q);
					}
					((Pow(OMEGA_INV, exp) % Q) * (Pow(OMEGA, exp) % Q)) % Q;
					{
						assert Pow(OMEGA_INV, exp) % Q == 0;
					}
					0;
				}
				assert false;
			}
		}
		r
	}

	function rev_omega_inv_powers_x_value(i: nat, d: pow2_t): (r: elem)
		ensures rev_omega_inv_powers_x_value_inner.requires(i, d) ==> r > 0
	{
		if rev_omega_inv_powers_x_value_inner.requires(i, d) then 
			rev_omega_inv_powers_x_value_inner(i, d)
		else
			0
	}

	function method {:axiom} rev_omega_inv_powers_mont_table(): (t: seq<elem>)
		ensures |t| == N.full;

	lemma {:axiom} rev_omega_inv_powers_mont_table_axiom(t: pow2_t, d: pow2_t, j: nat)
		requires t.exp < N.exp;
		requires j < t.full;
		requires t.full + j < N.full;
		requires d == pow2_half(PV.block_count(t));
		requires 2 * j < PV.block_size(d).full;
		ensures rev_omega_inv_powers_mont_table()[t.full + j] ==
			MQP.mqmul(rev_omega_inv_powers_x_value(2 * j, d), R);

	lemma rev_omega_inv_powers_mont_table_lemma(t: pow2_t, d: pow2_t, j: nat)
		requires t.exp < N.exp;
		requires j < t.full;
		requires d == pow2_half(PV.block_count(t));
		ensures t.full + j < N.full;
		ensures 2 * j < PV.block_size(d).full;
		ensures rev_omega_inv_powers_mont_table()[t.full + j] ==
			MQP.mqmul(rev_omega_inv_powers_x_value(2 * j, d), R);
	{
		var _ := twiddle_factors_index_bound_lemma(t, j);
		rev_omega_inv_powers_mont_table_axiom(t, d, j);
	}

	function method {:axiom} inverse_ntt_scaling_table(): (t: seq<elem>)
		ensures |t| == N.full;

	lemma {:axiom} inverse_ntt_scaling_table_axiom(i: nat)
		requires i < N.full;
		ensures inverse_ntt_scaling_table()[i] == MQP.mqmul(MQP.mqmul(MQP.mqpow(MQ.PSI_INV, i), MQ.N_INV), R);

}
