include "ntt_index.dfy"
include "ntt_params.dfy"

module mq_polys {
    import opened Seq
	import opened Power
    import Math

    import opened pows_of_2
    import opened ntt_index
    import opened ntt_512_params

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

    function a_i_times_x_to_the_i(a: seq<elem>, x: elem): seq<elem>
    {
        seq(|a|, i requires 0 <= i < |a| => mqmul(a[i], mqpow(x, i)))
        //Map(i => mqmul(a[i], mqpow(x, i)), a)
    }

    // function a_i_times_x_to_the_i_plus_k(a: seq<elem>, x: elem, k: nat): seq<elem>
    // {
    //     seq(|a|, i requires 0 <= i < |a| => mqmul(a[i], mqpow(x, i + k)))
    // }

    function mqsum(s: seq<elem>) : elem
    {
        //FoldRight((e1, e2) => mqadd(e1, e2), s, 0)
        if |s| == 0 then 0
        else mqadd(s[0], mqsum(s[1..]))
    }

    // lemma mqsum_adds(s1: seq<elem>, s2: seq<elem>) 
    //     ensures mqsum(s1 + s2) == mqadd(mqsum(s1), mqsum(s2))
    // {
    //     if |s1| == 0 {
    //         assert mqsum(s1) == 0;
    //         assert s1 + s2 == s2;
    //     } else {
    //         calc {
    //             mqsum(s1 + s2);
    //                 { assert (s1 + s2)[1..] == s1[1..] + s2; }
    //             mqadd(s1[0], mqsum(s1[1..] + s2));
    //                 { mqsum_adds(s1[1..], s2); }
    //             mqadd(s1[0], mqadd(mqsum(s1[1..]), mqsum(s2)));
    //                 { mqadd_associates(s1[0], mqsum(s1[1..]), mqsum(s2)); }
    //             mqadd(mqadd(s1[0], mqsum(s1[1..])), mqsum(s2));
    //             mqadd(mqsum(s1), mqsum(s2));
    //         }
    //     }
    // }
    
    function {:opaque} poly_eval(a: seq<elem>, x: elem): elem
    {
        mqsum(a_i_times_x_to_the_i(a, x))
    }

    lemma poly_eval_base_lemma(a: seq<elem>, x: elem)
        requires |a| == 1;
        ensures poly_eval(a, x) == a[0];
    {
        reveal poly_eval();
        calc == {
            poly_eval(a, x);
            mqsum(a_i_times_x_to_the_i(a, x));
            mqadd(a_i_times_x_to_the_i(a, x)[0], 0);
            a_i_times_x_to_the_i(a, x)[0];
            mqmul(a[0], mqpow(x, 0));
            {
                LemmaPow0Auto();
            }
            mqmul(a[0], 1);
            a[0];
        }
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

    function {:axiom} index_pairs(len1: nat, len2: nat, deg: nat): (r: seq<(nat, nat)>)
        requires deg < len1 + len2 - 1;
        ensures forall j: nat, k: nat :: (
            (j < len1 && k < len2 && j + k == deg)
                <==>
            (exists i: nat | i < |r| :: r[i] == (j, k)));
 
    function poly_mul_coef(a: seq<elem>, b: seq<elem>, deg: nat): elem
        requires deg < |a| + |b| - 1;
    {
        var pairs := index_pairs(|a|, |b|, deg);
        var terms := seq(|pairs|, i requires 0 <= i < |pairs| =>
            mqmul(a[pairs[i].0], b[pairs[i].1]));
        mqsum(terms)
    }

    function poly_mul(a: seq<elem>, b: seq<elem>): (c: seq<elem>)
    {
        if |a| == 0 || |b| == 0 then
            []
        else
            var len := |a| + |b| - 1;
            seq(len, i requires 0 <= i < len => poly_mul_coef(a, b, i))
    }

    function poly_zero_ext(a: seq<elem>, len: nat): (a': seq<elem>)
        requires |a| <= len; 
        ensures |a'| == len;
    {
        var ext := len - |a|;
        a + seq(ext, n requires 0 <= n < ext => 0)
    }

    function poly_add(a: seq<elem>, b: seq<elem>): (c: seq<elem>)
    {
        var len := Math.Max(|a|, |b|);
        var a := poly_zero_ext(a, len);
        var b := poly_zero_ext(b, len);
        seq(len, i requires 0 <= i < len => mqadd(a[i], b[i]))
    }

    predicate valid_poly_divmod(a: seq<elem>, b: seq<elem>, q: seq<elem>, r: seq<elem>)
    {
        && |r| < |b|
        && a == poly_add(poly_mul(q, b), r)
    }

    lemma {:axiom} poly_divmod_fundamental(a: seq<elem>, b: seq<elem>)
        requires |b| > 0;
        ensures exists q: seq<elem>, r: seq<elem> :: valid_poly_divmod(a, b, q, r)

    function poly_mod(a: seq<elem>, m: seq<elem>): (r: seq<elem>)
        requires |m| > 0;
    {
        poly_divmod_fundamental(a, m);
        var q: seq<elem>, r: seq<elem> :| valid_poly_divmod(a, m, q, r);
        r
    }

    predicate poly_mod_equiv(a: seq<elem>, b: seq<elem>, m: seq<elem>)
        requires |m| > 0;
    {
        poly_mod(a, m) == poly_mod(b, m)
    }

    function forward_product(a: n_sized, b: n_sized): n_sized
    {
        seq(N.full, i requires 0 <= i < N.full => 
            (var x := mqpow(PSI, 2 * i + 1);
            mqmul(poly_eval(a, x), poly_eval(b, x))))
    }

    function negatively_wrapped_convolution(a: n_sized, b: n_sized, p: n_sized): n_sized
        requires p == forward_product(a, b);
    {
        seq(N.full, i requires 0 <= i < N.full => 
            (var x := mqpow(OMEGA_INV, i);
            (poly_eval(p, x) * mqpow(PSI_INV, i) * N_INV) % Q))
    }

    function n_ideal(): seq<elem>
    {
        [1] + seq(N.full - 1, i requires 0 <= i < N.full - 1 => 0) + [1]
    }

    lemma {:axiom} negatively_wrapped_convolution_lemma(a: n_sized, b: n_sized, p: n_sized, c: n_sized)
        requires p == forward_product(a, b);
        requires c == negatively_wrapped_convolution(a, b, p);
        ensures poly_mod_equiv(c, poly_mul(a, b), n_ideal());
}
