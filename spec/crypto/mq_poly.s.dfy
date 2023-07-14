include "ntt_param.s.dfy"

abstract module mq_poly_s(MQNTT: ntt_param_s) {
    import opened Seq
    import opened Power
    import opened Mul
    import opened DivMod
    import opened Power2
    import Math

    import opened pow2_s

    type elem = MQNTT.elem
    type elems = MQNTT.elems

    const Q := MQNTT.Q;
    ghost const N := MQNTT.N; 

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

    function method {:axiom} montmul(a: elem, b: elem): (c: elem)
        ensures c == (a * b * MQNTT.R_INV) % Q

    function poly_terms(a: seq<elem>, x: elem): seq<elem>
    {
        seq(|a|, i requires 0 <= i < |a| => mqmul(a[i], mqpow(x, i)))
    }

    function mqsum(s: seq<elem>): elem
    {
        if |s| == 0 then 0
        else mqadd(s[0], mqsum(s[1..]))
    }

    function poly_eval(a: seq<elem>, x: elem): elem
    {
        mqsum(poly_terms(a, x))
    }

    function poly_zero_ext(a: seq<elem>, len: nat): (a': seq<elem>)
        requires |a| <= len; 
        ensures |a'| == len;
    {
        var ext := len - |a|;
        a + seq(ext, n requires 0 <= n < ext => 0)
    }

    function zero_poly(n: nat): (a': seq<elem>)
    {
        seq(n, i requires 0 <= i < n => 0)
    }

    function poly_add(a: seq<elem>, b: seq<elem>): (c: seq<elem>)
    {
        var len := Math.Max(|a|, |b|);
        var a := poly_zero_ext(a, len);
        var b := poly_zero_ext(b, len);
        seq(len, i requires 0 <= i < len => mqadd(a[i], b[i]))
    }

    function poly_sub(a: seq<elem>, b: seq<elem>): (c: seq<elem>)
    {
        var len := Math.Max(|a|, |b|);
        var a := poly_zero_ext(a, len);
        var b := poly_zero_ext(b, len);
        seq(len, i requires 0 <= i < len => mqsub(a[i], b[i]))
    }

    predicate exists_in_index_pairs(i:nat, j:nat, r: seq<(nat, nat)>)
    {
        exists k: nat | k < |r| :: r[k] == (i, j)
    }

    function index_pairs(len1: nat, len2: nat, deg: nat): (r: seq<(nat, nat)>)
        requires deg < len1 + len2 - 1;
        ensures forall j: nat, k: nat :: (
            (j < len1 && k < len2 && j + k == deg)
                <==>
            exists_in_index_pairs(j, k, r));
    // refinement obligation 
 
    function poly_mul_coef(a: seq<elem>, b: seq<elem>, deg: nat): elem
        requires deg < |a| + |b| - 1;
    {
        var pairs := index_pairs(|a|, |b|, deg);
        var terms := seq(|pairs|, i requires 0 <= i < |pairs| =>
            assert exists_in_index_pairs(pairs[i].0, pairs[i].1, pairs);
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

    predicate valid_poly_divmod(a: seq<elem>, b: seq<elem>, q: seq<elem>, r: seq<elem>)
    {
        && |r| < |b|
        && a == poly_add(poly_mul(q, b), r)
    }

    lemma {:axiom} poly_fundamental_divmod_lemma(a: seq<elem>, b: seq<elem>)
        requires b != zero_poly(|b|);
        ensures exists q: seq<elem>, r: seq<elem> :: valid_poly_divmod(a, b, q, r)

    function poly_mod(a: seq<elem>, m: seq<elem>): (r: seq<elem>)
        requires m != zero_poly(|m|);
    {
        poly_fundamental_divmod_lemma(a, m);
        var q: seq<elem>, r: seq<elem> :| valid_poly_divmod(a, m, q, r);
        r
    }

    function circle_product(a: elems, b: elems): elems
    {
        seq(N.full, i requires 0 <= i < N.full => mqmul(a[i], b[i]))
    }

    function NTT(a: elems): elems
    {
        seq(N.full, i requires 0 <= i < N.full =>
            poly_eval(a, mqpow(MQNTT.OMEGA, i)))
    }

    function INTT(a: elems): elems
    {
        seq(N.full, i requires 0 <= i < N.full =>
            mqmul(poly_eval(a, mqpow(MQNTT.OMEGA_INV, i)), MQNTT.N_INV))
    }

    function scaled_coeff(a: elems): elems
    {
        seq(N.full, i requires 0 <= i < N.full =>
            mqmul(a[i], mqpow(MQNTT.PSI, i)))
    }

    function negatively_wrapped_convolution(a: elems, b: elems): elems
    {
        var inverse :seq<elem> :=
            INTT(circle_product(NTT(scaled_coeff(a)), NTT(scaled_coeff(b))));
        seq(N.full, i requires 0 <= i < N.full =>
            mqmul(inverse[i], mqpow(MQNTT.PSI_INV, i)))
    }

    function n_ideal(): (r: seq<elem>)
        ensures r != zero_poly(|r|);
    {
        var r := [1] + seq(N.full - 1, i requires 0 <= i < N.full - 1 => 0) + [1];
        assert r[0] != 0;
        r
    }

    lemma {:axiom} negatively_wrapped_convolution_lemma(a: elems, b: elems, p: elems)
        requires p == negatively_wrapped_convolution(a, b);
        ensures p == poly_mod(poly_mul(a, b), n_ideal())
}
