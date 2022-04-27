include "polys.dfy"
include "pow2.dfy"
include "ntt_index.dfy"

abstract module nth_root {
	import opened Power
	import opened Power2
	import opened DivMod
	import opened Mul

	import opened pows_of_2
    import opened ntt_index
	import opened ntt_polys

	const N: pow2_t;
	const PSI: elem;
	const PSI_INV: elem;
	const OMEGA: elem;
	const OMEGA_INV: elem;
	const R: elem;
	const R_INV: elem;

	type n_sized = s: seq<elem>
        | |s| == N.full witness *

	function method {:axiom} montmul(a: elem, b: elem): (c: elem)
		ensures c == (a * b * R_INV) % Q

	// obligations
	lemma Nth_root_lemma()
		ensures N.exp >= 2;
		ensures Pow(PSI, 2 * N.full) % Q == 1
		ensures Pow(PSI, N.full) % Q == Q - 1
		ensures (PSI * PSI_INV) % Q == 1

		ensures Pow(OMEGA, N.full) % Q == 1
		ensures Pow(OMEGA_INV, pow2_half(N).full) % Q == Q - 1
		ensures (OMEGA * OMEGA_INV) % Q == 1

		ensures (R_INV * R) % Q == 1

	function method block_count(m: pow2_t): pow2_t
		requires 0 <= m.exp <= N.exp;
	{
		pow2_div(N, m)
	}

	function method block_size(c: pow2_t): pow2_t
		requires 0 <= c.exp <= N.exp;
	{
		pow2_div(N, c)
	}

	// lemma block_count_product_lemma(m: pow2_t)
	// 	requires 0 <= m.exp <= N.exp;
	// 	ensures block_count(m).full * m.full == N.full;
	// {
	// }

	lemma block_count_half_lemma(m: pow2_t)
		requires 1 <= m.exp <= N.exp;
		ensures block_count(pow2_half(m)) == pow2_double(block_count(m));
	{
		var left := pow2_div(N, pow2_half(m));
		assert left.full * (m.full / 2) == N.full;
		var right := pow2_div(N, m);
		var half := m.full / 2;
		pow2_basics(m);

		calc == {
			left.full * half;
			left.full * (m.full / 2);
			right.full * (2 * half);
			{
				LemmaMulIsAssociativeAuto();
			}
			(right.full * 2) * half;
		}
		LemmaMulEqualityConverse(half, left.full, right.full * 2);
	}

	predicate {:opaque} unifromly_sized(blocks: seq<seq<elem>>, bsize: pow2_t)
		requires bsize.exp <= N.exp;
		ensures unifromly_sized(blocks, bsize)
			==> |blocks| == block_count(bsize).full;
	{
		&& (forall i: nat | i < |blocks| :: |blocks[i]| == bsize.full)
		&& |blocks| == block_count(bsize).full
	}

	lemma unifromly_sized_instance_lemma(blocks: seq<seq<elem>>, bsize: pow2_t, i: nat)
		requires bsize.exp <= N.exp;
		requires unifromly_sized(blocks, bsize);
		requires i < |blocks|;
		ensures |blocks[i]| == bsize.full;
	{
		reveal unifromly_sized();
	}

	lemma point_view_index_bound_lemma(i: nat, j: nat, bsize: pow2_t)
		requires bsize.exp <= N.exp;
		requires i < block_count(bsize).full;
		requires j < bsize.full;
		ensures 0 <= i + j * block_count(bsize).full < N.full;
	{
		var count := block_count(bsize).full;
		calc {
			i + j * count;
			<=
			count - 1 + j * count;
			<= { LemmaMulInequality(j, bsize.full - 1, count); }
			count - 1 + (bsize.full - 1) * count;
			{ LemmaMulIsDistributive(count, bsize.full, 1); }
			count - 1 + bsize.full * count - count;
			bsize.full * count - 1;
			N.full - 1;
		}
		LemmaMulStrictlyPositiveAuto();
	}

	function point_view_index(i: nat, j: nat, bsize: pow2_t): (offset: nat)
		requires bsize.exp <= N.exp;
		requires i < block_count(bsize).full;
		requires j < bsize.full;
		ensures offset < N.full;
	{
		point_view_index_bound_lemma(i, j, bsize);
		i + j * block_count(bsize).full
	}

	lemma point_view_index_disjont_lemma(i: nat, j: nat, i': nat, j': nat, bsize: pow2_t)
		requires bsize.exp <= N.exp;
		requires i < block_count(bsize).full;
		requires j < bsize.full;
		requires i' < block_count(bsize).full;
		requires j' < bsize.full;
		requires i != i' || j != j';
		ensures point_view_index(i, j, bsize) != point_view_index(i', j', bsize);
	{
		var offset := point_view_index(i, j, bsize);
		var offset' := point_view_index(i', j', bsize);
		var count := block_count(bsize).full;

		if i != i' && offset == offset' {
			LemmaFundamentalDivModConverse(offset, count, j, i);
			LemmaFundamentalDivModConverse(offset, count, j', i');
			assert false;
			return;
		}

		if j != j' && offset == offset' {
			assert i == i';
			assert j * count == j' * count;
			LemmaMulIsCommutativeAuto();
			LemmaMulEqualityConverse(count, j', j);
			assert false;
		}
	}

	function points_view(a: n_sized, i: nat, bsize: pow2_t): (v: seq<elem>)
        requires bsize.exp <= N.exp;
        requires i < block_count(bsize).full;
        // ensures |v| == bsize.full;
    {
        var size := bsize.full;
        seq(size, j requires 0 <= j < size => a[point_view_index(i, j, bsize)])
    }

    // interpret an n_sized buffer as a level view
    // contains blocks of points, each block has bsize
    function level_points_view(a: n_sized, bsize: pow2_t): (vs: seq<seq<elem>>)
        requires bsize.exp <= N.exp;
        ensures unifromly_sized(vs, bsize);
    {
        var count := block_count(bsize).full;
        var vs := seq(count, i requires 0 <= i < count => points_view(a, i, bsize));
        assert unifromly_sized(vs, bsize) by {
            reveal unifromly_sized();
        }
        vs
    }

	function method {:opaque} build_lower_level(higher: seq<seq<elem>>, bsize: pow2_t): (lower: seq<seq<elem>>)
		requires 1 <= bsize.exp <= N.exp;
		requires unifromly_sized(higher, bsize);
		ensures unifromly_sized(lower, pow2_half(bsize));
	{
		reveal unifromly_sized();
		pow2_basics(bsize);
		block_count_half_lemma(bsize);
		var new_size := pow2_half(bsize);
		var new_count := |higher| * 2;
		seq(new_count, n requires 0 <= n < new_count => 
			if n % 2 == 0 then even_indexed_items(higher[n/2], bsize)
			else odd_indexed_items(higher[n/2], bsize))
	}

	function method {:opaque} build_higher_level(lower: seq<seq<elem>>, bsize: pow2_t): (higher: seq<seq<elem>>)
		requires 0 <= bsize.exp < N.exp;
		requires unifromly_sized(lower, bsize);
		ensures unifromly_sized(higher, pow2_double(bsize));
	{
		reveal unifromly_sized();
		pow2_basics(bsize);
		var new_size := pow2_double(bsize);
		block_count_half_lemma(new_size);
		var new_count := |lower| / 2;
		seq(new_count, n requires 0 <= n < new_count => 
			merge_even_odd_indexed_items(lower[n*2], lower[n*2+1], bsize))
	}

	lemma build_higher_inverse_lemma(lower: seq<seq<elem>>, bsize: pow2_t)
		requires 0 <= bsize.exp < N.exp;
		requires unifromly_sized(lower, bsize);
		ensures build_lower_level(build_higher_level(lower, bsize), pow2_double(bsize)) == lower;
	{
		reveal build_higher_level();
		reveal build_lower_level();
		var higher := build_higher_level(lower, bsize);
		var new_size := pow2_double(bsize);
		assert build_lower_level(higher, new_size) == lower;
	}

	lemma poly_base_level_correct_lemma(coeffs: n_sized)
		ensures unifromly_sized([coeffs], pow2(N.exp));
	{
		reveal unifromly_sized();
		assert |coeffs| == N.full;
	}

	// construct polys level view 
	// each block is a poly, has bsize coefficients
	function level_polys(coeffs: n_sized, bsize: pow2_t): (lps: seq<seq<elem>>)
		requires 0 <= bsize.exp <= N.exp;
		decreases N.exp - bsize.exp;
		ensures unifromly_sized(lps, bsize);
	{
		if bsize.exp == N.exp then
			poly_base_level_correct_lemma(coeffs);
			[coeffs]
		else
			var double_size := pow2_double(bsize);
			var higher := level_polys(coeffs,double_size);
			build_lower_level(higher, double_size)
	}

	lemma level_polys_index_correspondence_lemma(
		higher: seq<seq<elem>>, hi_size: pow2_t, i: nat, 
		lower: seq<seq<elem>>)
		requires 1 <= hi_size.exp <= N.exp;
		requires i < |higher|;
		requires unifromly_sized(higher, hi_size);
		requires build_lower_level(higher, hi_size) == lower;
		ensures |higher[i]| == hi_size.full;
		ensures 2 * i + 1 < |lower|;
		ensures even_indexed_items(higher[i], hi_size) == lower[2 * i];
		ensures odd_indexed_items(higher[i], hi_size) == lower[2 * i + 1];
		ensures |lower[2 * i]| == |lower[2 * i + 1]| == pow2_half(hi_size).full;
	{
		reveal unifromly_sized();
		reveal build_lower_level();
	}

	type x_fun = (nat, pow2_t) --> elem

	predicate {:opaque} points_eval_prefix_inv(points: seq<elem>, poly: seq<elem>, x_value: x_fun, l: nat, count: pow2_t)
	{
		&& count.exp <= N.exp
		&& l <= |points| == |poly| == block_size(count).full
		&& (forall i | 0 <= i < l :: 
			(&& x_value.requires(i, count)
			&& poly_eval(poly, x_value(i, count)) == points[i]))
	}

	lemma points_eval_prefix_inv_vacuous_lemma(points: seq<elem>, poly: seq<elem>, x_value: x_fun, count: pow2_t)
		requires count.exp <= N.exp;
		requires |points| == |poly| == block_size(count).full;
		ensures points_eval_prefix_inv(points, poly, x_value, 0, count);
	{
		forall i | 0 <= i < 0 
			ensures poly_eval(poly, x_value(i, count)) == points[i];
		{
		}
		reveal points_eval_prefix_inv();
	}

	// d is the block count
	predicate {:opaque} points_eval_suffix_inv(points: seq<elem>, poly: seq<elem>, x_value: x_fun, l: nat, count: pow2_t)
	{
		&& count.exp <= N.exp
		&& l <= |points| == |poly| == block_size(count).full
		&& (forall i | l <= i < block_size(count).full ::
			(&& x_value.requires(i, count)
			&& poly_eval(poly, x_value(i, count)) == points[i]))
	}

	predicate points_eval_inv(points: seq<elem>, poly: seq<elem>, x_value: x_fun, count: pow2_t)
	{
		points_eval_suffix_inv(points, poly, x_value, 0, count)
	}

	lemma primitive_root_non_zero_lemma(i: nat)
		requires i < N.full * 2;
		ensures mqpow(PSI, i) != 0;
	{
		var PSI := PSI;
		if Pow(PSI, i) % Q == 0 {
			var j := N.full * 2 - i;
			calc == {
				1;
				{
					Nth_root_lemma();
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
		ensures mqpow(PSI, a + 2 * N.full) == mqpow(PSI, a);
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
				Nth_root_lemma();
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
		ensures mqpow(OMEGA_INV, a + N.full) == mqpow(OMEGA_INV, a);
	{
		var N := N.full;
		Nth_root_lemma();

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
			((Pow(OMEGA, N) % Q) * (Pow(OMEGA_INV, N)) % Q) % Q;
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
		ensures Pow(PSI, a + N.full) % Q == (Q - Pow(PSI, a)) % Q;
	{
		var PSI := PSI;
		var N := N.full;
		calc == {
			Pow(PSI, a + N) % Q;
			{
				LemmaPowAdds(PSI, a, N);
			}
			(Pow(PSI, a) * Pow(PSI, N)) % Q;
			{
				LemmaMulModNoopGeneral(Pow(PSI, a), Pow(PSI, N), Q);
			}
			((Pow(PSI, a) % Q) * (Pow(PSI, N) % Q)) % Q;
			{
				Nth_root_lemma();
				assert Pow(PSI, N) % Q == Q - 1;
			}
			((Pow(PSI, a) % Q) * (Q - 1)) % Q;
			{
				LemmaMulIsDistributive(Pow(PSI, a) % Q, Q, 1);
			}
			((Pow(PSI, a) % Q) * Q - Pow(PSI, a) % Q) % Q;
			{
				LemmaModMultiplesVanish((Pow(PSI, a) % Q), -Pow(PSI, a) % Q, Q);
			}
			(- Pow(PSI, a) % Q) % Q;
			{
				LemmaModBasicsAuto();
			}
			(- Pow(PSI, a)) % Q;
			{
				LemmaModMultiplesVanish(1, - Pow(PSI, a), Q);
			}
			(Q - Pow(PSI, a)) % Q;
		}
	}

	lemma inv_half_rotation_lemma(a: nat)
		ensures (N.full / 2) * 2 == N.full;
		ensures Pow(OMEGA_INV, a + N.full / 2) % Q == (Q - Pow(OMEGA_INV, a)) % Q;
	{
		Nth_root_lemma();
		pow2_basics(N);
		var HN := N.full / 2;

		calc == {
			Pow(OMEGA_INV, a + HN) % Q;
			{
				LemmaPowAdds(OMEGA_INV, a, HN);
			}
			(Pow(OMEGA_INV, a) * Pow(OMEGA_INV, HN)) % Q;
			{
				LemmaMulModNoopGeneral(Pow(OMEGA_INV, a), Pow(OMEGA_INV, HN), Q);
			}
			((Pow(OMEGA_INV, a) % Q) * (Pow(OMEGA_INV, HN) % Q)) % Q;
			{
				Nth_root_lemma();
				assert Pow(OMEGA_INV, HN) % Q == Q - 1;
			}
			((Pow(OMEGA_INV, a) % Q) * (Q - 1)) % Q;
			{
				LemmaMulIsDistributive(Pow(OMEGA_INV, a) % Q, Q, 1);
			}
			((Pow(OMEGA_INV, a) % Q) * Q - Pow(OMEGA_INV, a) % Q) % Q;
			{
				LemmaModMultiplesVanish((Pow(OMEGA_INV, a) % Q), -Pow(OMEGA_INV, a) % Q, Q);
			}
			(- Pow(OMEGA_INV, a) % Q) % Q;
			{
				LemmaModBasicsAuto();
			}
			(- Pow(OMEGA_INV, a)) % Q;
			{
				LemmaModMultiplesVanish(1, - Pow(OMEGA_INV, a), Q);
			}
			(Q - Pow(OMEGA_INV, a)) % Q;
		}
	}

	lemma twiddle_factors_index_bound_lemma(t: pow2_t, j: nat)
		returns (d: pow2_t)
		requires t.exp < N.exp;
		requires j < t.full;
		ensures t.full + j < N.full;
		ensures d == pow2_half(block_count(t));
		ensures 2 * j < block_size(d).full;
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

		d := block_count(t);
		assert block_size(d) == t;

		calc {
			2 * j;
			<
			2 * t.full;
			2 * block_size(d).full;
			pow2_double(block_size(d)).full;
			{
				block_count_half_lemma(d);
			}
			block_size(pow2_half(d)).full;
		}

		d := pow2_half(block_count(t));
	}

	// d is the block count
	// i is the offset in the block
	function method rev_mixed_powers_mont_x_value(i: nat, d: pow2_t): (r: elem)
		requires d.exp <= N.exp;
		requires i < block_size(d).full;
		ensures r > 0;
	{
		var bound := block_size(d);
		LemmaMulNonnegative(2 * bit_rev_int(i, bound), d.full);
		var r := mqpow(PSI, 2 * bit_rev_int(i, bound) * d.full + d.full);
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
			// 	block_count_product_lemma(bound);
			// }
			2 * N.full - d.full;
		}
		primitive_root_non_zero_lemma(2 * bit_rev_int(i, bound) * d.full + d.full);
		r
	}

	function {:axiom} rev_mixed_powers_mont_table(): (t: n_sized)
	
	lemma {:axiom} rev_mixed_powers_mont_table_axiom(t: pow2_t, d: pow2_t, j: nat)
		requires t.exp < N.exp;
		requires j < t.full;
		requires t.full + j < N.full;
		requires d == pow2_half(block_count(t));
		requires 2 * j < block_size(d).full;
		ensures rev_mixed_powers_mont_table()[t.full + j] ==
			mqmul(rev_mixed_powers_mont_x_value(2 * j, d), R);

	lemma rev_mixed_powers_mont_table_lemma(t: pow2_t, d: pow2_t, j: nat)
		requires t.exp < N.exp;
		requires j < t.full;
		requires d == pow2_half(block_count(t));
		ensures t.full + j < N.full;
		ensures 2 * j < block_size(d).full;
		ensures rev_mixed_powers_mont_table()[t.full + j] ==
			mqmul(rev_mixed_powers_mont_x_value(2 * j, d), R);
	{
		var _ := twiddle_factors_index_bound_lemma(t, j);
		rev_mixed_powers_mont_table_axiom(t, d, j);
	}

	// d is the block count
	// i is the offset in the block
	function method rev_omega_inv_powers_x_value(i: nat, d: pow2_t): (r: elem)
		requires d.exp <= N.exp;
		requires i < block_size(d).full;
		ensures r > 0;
	{
		var bound := block_size(d);
		LemmaMulNonnegative(bit_rev_int(i, bound), d.full);
		var r := mqpow(OMEGA_INV, bit_rev_int(i, bound) * d.full);
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
						Nth_root_lemma();
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

	function {:axiom} rev_omega_inv_powers_mont_table(): (t: n_sized)

	lemma {:axiom} rev_omega_inv_powers_mont_table_axiom(t: pow2_t, d: pow2_t, j: nat)
		requires t.exp < N.exp;
		requires j < t.full;
		requires t.full + j < N.full;
		requires d == pow2_half(block_count(t));
		requires 2 * j < block_size(d).full;
		ensures rev_omega_inv_powers_mont_table()[t.full + j] ==
			mqmul(rev_omega_inv_powers_x_value(2 * j, d), R);

	lemma rev_omega_inv_powers_mont_table_lemma(t: pow2_t, d: pow2_t, j: nat)
		requires t.exp < N.exp;
		requires j < t.full;
		requires d == pow2_half(block_count(t));
		ensures t.full + j < N.full;
		ensures 2 * j < block_size(d).full;
		ensures rev_omega_inv_powers_mont_table()[t.full + j] ==
			mqmul(rev_omega_inv_powers_x_value(2 * j, d), R);
	{
		var _ := twiddle_factors_index_bound_lemma(t, j);
		rev_omega_inv_powers_mont_table_axiom(t, d, j);
	}


}
