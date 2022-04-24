include "ntt_index.dfy"

module ntt_polys {
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
