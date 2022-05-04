include "ntt_index.dfy"

module mq_polys {
    import opened Seq
	import opened Power

    import opened pows_of_2
    import opened ntt_index

	const Q: nat := 12289

	type elem = i :nat | i < Q

	function method mqpow(a: elem, b: nat): elem
	{
		Pow(a, b) % Q
	}

	function method mqmul(a: elem, b: elem): elem
	{
		(a * b) % Q
	}

	function method mqadd(a: elem, b: elem): elem
	{
		(a + b) % Q
	}

	function method mqsub(a: elem, b: elem): elem
	{
		(a - b) % Q
	}

    function method {:opaque} even_indexed_items<T>(a: seq<T>, len: pow2_t): seq<T>
        requires |a| == len.full;
    {
        pow2_basics(len);
        seq(len.full/2, n requires 0 <= n < len.full/2 => a[n * 2])
    }

    function method {:opaque} odd_indexed_items<T>(a: seq<T>, len: pow2_t): seq<T>
        requires |a| == len.full;
    {
        pow2_basics(len);
        seq(len.full/2, n requires 0 <= n < len.full/2 => a[n * 2 + 1])
    }

    function method {:opaque} merge_even_odd_indexed_items<T>(a: seq<T>, b: seq<T>, len: pow2_t): (r: seq<T>)
        requires |a| == |b| == len.full;
        ensures |r| == pow2_double(len).full;
        ensures even_indexed_items(r, pow2_double(len)) == a;
        ensures odd_indexed_items(r, pow2_double(len)) == b;
    {
        pow2_basics(len);
        var new_len := pow2_double(len);
        var r := seq(new_len.full, n requires 0 <= n < new_len.full => 
            if n % 2 == 0 then a[n/2] else b[n/2]);
        assert even_indexed_items(r, new_len) == a by {
            reveal even_indexed_items();
        }
        assert odd_indexed_items(r, new_len) == b by {
            reveal odd_indexed_items();
        }
        r
    }

    function {:opaque} poly_eval(a: seq<elem>, x: elem): elem
    {
        if |a| == 0 then 0
        else mqadd(First(a), mqmul(poly_eval(DropFirst(a), x), x))
    }

    lemma poly_eval_base_lemma(a: seq<elem>, x: elem)
        requires |a| == 1;
        ensures poly_eval(a, x) == a[0];
    {
        reveal poly_eval();
    }

    lemma {:axiom} poly_eval_split_lemma(a: seq<elem>, 
        a_e: seq<elem>, a_o: seq<elem>, len: pow2_t, x: elem)
        requires |a| == len.full >= 2;
        requires a_e == even_indexed_items(a, len)
        requires a_o == odd_indexed_items(a, len)
        ensures var sqr := mqmul(x, x);
            poly_eval(a, x)
                == 
            mqadd(poly_eval(a_e, sqr), mqmul(x, poly_eval(a_o, sqr)));
        decreases |a|;

    // predicate {:opaque} poly_eval_all_points(a: seq<elem>, y: seq<elem>, len: pow2_t)
    //     requires 0 <= len.exp <= L;
    //     ensures poly_eval_all_points(a, y, len) ==> |y| == |a| == len.full;
    // {
    //     && |y| == |a| == len.full
    //     && (forall i: nat | i < len.full ::
    //         y[i] == poly_eval(a, omega_nk(len, i)))
    // }

    // lemma poly_eval_all_points_lemma(a: seq<elem>, y: seq<elem>, len: pow2_t, i: nat)
    //     requires 0 <= len.exp <= L;
    //     requires poly_eval_all_points(a, y, len);
    //     requires i < len.full;
    //     ensures  y[i] == poly_eval(a, omega_nk(len, i));
    // {
    //     reveal poly_eval_all_points();
    // }
}
