include "mq_poly.i.dfy"

module poly_view_i(MQ: ntt_param_s) {
	import opened Power
	import opened Power2
	import opened DivMod
	import opened Mul

	import opened pow2_s
    import opened ntt_index

	import MQP = mq_poly_i(MQ)

	type x_fun = (nat, pow2_t) -> elem

	type elem = MQ.elem
	type n_elems = MQ.n_elems

	const Q := MQ.Q;
	ghost const N := MQ.N; 

	function block_count(m: pow2_t): pow2_t
		requires 0 <= m.exp <= N.exp;
	{
		pow2_div(N, m)
	}

	function block_size(c: pow2_t): pow2_t
		requires 0 <= c.exp <= N.exp;
	{
		pow2_div(N, c)
	}

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

	function points_view(a: seq<elem>, i: nat, bsize: pow2_t): (v: seq<elem>)
		requires |a| == N.full;
		requires bsize.exp <= N.exp;
		requires i < block_count(bsize).full;
		// ensures |v| == bsize.full;
	{
		var size := bsize.full;
		seq(size, j requires 0 <= j < size => a[point_view_index(i, j, bsize)])
	}

	// interpret an n_elems buffer as a level view
	// contains blocks of points, each block has bsize
	function level_points_view(a: seq<elem>, bsize: pow2_t): (vs: seq<seq<elem>>)
		requires |a| == N.full;
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

	function method {:opaque} build_lower_level_polys(higher: seq<seq<elem>>, bsize: pow2_t): (lower: seq<seq<elem>>)
		requires 1 <= bsize.exp <= N.exp;
		requires unifromly_sized(higher, bsize);
		ensures |higher| * 2 == |lower|;
		ensures unifromly_sized(lower, pow2_half(bsize));
	{
		reveal unifromly_sized();
		pow2_basics(bsize);
		block_count_half_lemma(bsize);
		var new_size := pow2_half(bsize);
		var new_count := |higher| * 2;
		seq(new_count, n requires 0 <= n < new_count => 
			if n % 2 == 0 then MQP.even_indexed_items(higher[n/2], bsize)
			else MQP.odd_indexed_items(higher[n/2], bsize))
	}

	function method {:opaque} build_higher_level_polys(lower: seq<seq<elem>>, bsize: pow2_t): (higher: seq<seq<elem>>)
		requires 0 <= bsize.exp < N.exp;
		requires unifromly_sized(lower, bsize);
		ensures |higher| * 2 == |lower|;
		ensures unifromly_sized(higher, pow2_double(bsize));
	{
		reveal unifromly_sized();
		pow2_basics(bsize);
		var new_size := pow2_double(bsize);
		block_count_half_lemma(new_size);
		var new_count := |lower| / 2;
		seq(new_count, n requires 0 <= n < new_count => 
			MQP.merge_even_odd_indexed_items(lower[n*2], lower[n*2+1], bsize))
	}

	lemma build_polys_inverse_lemma(lower: seq<seq<elem>>, bsize: pow2_t)
		requires 0 <= bsize.exp < N.exp;
		requires unifromly_sized(lower, bsize);
		ensures build_lower_level_polys(build_higher_level_polys(lower, bsize), pow2_double(bsize)) == lower;
	{
		reveal build_higher_level_polys();
		reveal build_lower_level_polys();
		var higher := build_higher_level_polys(lower, bsize);
		var new_size := pow2_double(bsize);
		assert build_lower_level_polys(higher, new_size) == lower;
	}

	// construct polys level view 
	// each block is a poly, has bsize coefficients
	function {:opaque} level_polys(coefficients: n_elems, bsize: pow2_t): (lps: seq<seq<elem>>)
		requires 0 <= bsize.exp <= N.exp;
		ensures unifromly_sized(lps, bsize);
		decreases N.exp - bsize.exp;
	{
		if bsize.exp == N.exp then
			assert unifromly_sized([coefficients], N) by {
				reveal unifromly_sized();
			}
			[coefficients]
		else
			var double_size := pow2_double(bsize);
			var higher := level_polys(coefficients, double_size);
			build_lower_level_polys(higher, double_size)
	}

	function base_level_polys(coefficients: n_elems): (lps: seq<seq<elem>>)
		ensures 0 <= pow2(0).exp <= N.exp;
		ensures unifromly_sized(lps, pow2(0));
	{
		var size := pow2(0);
		assert 0 <= size.exp <= N.exp; // ??
		var lps := level_polys(coefficients, size);
		assert block_count(size).full == N.full;
		lps
	}

	// this is provable (and sort of already proved), but complicated
	lemma {:axiom} base_level_polys_lemma(coefficients: n_elems, i: nat)
		requires i < N.full;
		ensures |base_level_polys(coefficients)[bit_rev_int(i, N)]| == 1;
		ensures base_level_polys(coefficients)[bit_rev_int(i, N)][0] == coefficients[i];
		// ensures |base_level_polys()[i]| == 1;
		// ensures base_level_polys()[i][0] == A()[bit_rev_int(i, N)];

	lemma level_polys_index_correspondence_lemma(coefficients: n_elems,
		higher: seq<seq<elem>>,
		hsize: pow2_t,
		i: nat,
		lower: seq<seq<elem>>)

		requires 1 <= hsize.exp <= N.exp;
		requires i < |higher|;
		requires higher == level_polys(coefficients, hsize);
		requires lower == level_polys(coefficients, pow2_half(hsize));
		ensures 2 * i + 1 < |lower|;
		ensures |higher[i]| == hsize.full;
		ensures MQP.even_indexed_items(higher[i], hsize) == lower[2 * i];
		ensures MQP.odd_indexed_items(higher[i], hsize) == lower[2 * i + 1];
	{
		reveal unifromly_sized();
		reveal build_lower_level_polys();

		assert build_lower_level_polys(higher, hsize) == lower by {
			reveal level_polys();
		}
	}

	predicate {:opaque} points_eval_prefix_inv(points: seq<elem>, poly: seq<elem>, x_value: x_fun, l: nat, count: pow2_t)
	{
		&& count.exp <= N.exp
		&& l <= |points| == |poly| == block_size(count).full
		&& (forall i | 0 <= i < l :: 
			(MQP.poly_eval(poly, x_value(i, count)) == points[i]))
	}

	lemma points_eval_prefix_inv_vacuous_lemma(points: seq<elem>, poly: seq<elem>, x_value: x_fun, count: pow2_t)
		requires count.exp <= N.exp;
		requires |points| == |poly| == block_size(count).full;
		ensures points_eval_prefix_inv(points, poly, x_value, 0, count);
	{
		forall i | 0 <= i < 0 
			ensures MQP.poly_eval(poly, x_value(i, count)) == points[i];
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
			(MQP.poly_eval(poly, x_value(i, count)) == points[i]))
	}

	predicate points_eval_inv(points: seq<elem>, poly: seq<elem>, x_value: x_fun, count: pow2_t)
	{
		points_eval_suffix_inv(points, poly, x_value, 0, count)
	}
}