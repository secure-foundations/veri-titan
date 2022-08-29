include "ntt_param.s.dfy"

module mq_norm_s(MQ: ntt_param_s) {
    const Q_HLAF := MQ.Q / 2

    predicate int_is_normalized(e: int)
    {
        -Q_HLAF <= e <= Q_HLAF
    }

    type nelem = e: int | int_is_normalized(e)

    // 0 <= e < Q -> -Q/2 <= e <= Q/2
    function normalize(e: MQ.elem): nelem
    {
        if e <= Q_HLAF then e else e as int - MQ.Q
    }

    function normalize_elems(s: seq<MQ.elem>): seq<nelem>
    {
        seq(|s|, i requires 0 <= i < |s| => normalize(s[i]))
    }

    // -Q/2 <= e < Q/2 -> 0 <= e <= Q 
    function denormalize(e: nelem): MQ.elem
    {
        if e >= 0 then e else e + MQ.Q
    }

    function denormalize_nelems(s: seq<nelem>): seq<MQ.elem>
    {
        seq(|s|, i requires 0 <= i < |s| => denormalize(s[i]))
    }

    lemma normalize_inverse(e: MQ.elem)
        ensures denormalize(normalize(e)) == e;
    {}

    lemma denormalize_inverse(e: nelem)
        ensures normalize(denormalize(e)) == e;
    {
    }

    lemma square_positive_lemma(a: int)
        ensures a * a >= 0;

    function l2norm_squared(s1: seq<nelem>, s2: seq<nelem>, i: nat): nat
        requires |s1| == |s2|
        requires i <= |s1|
    {
        if i == 0 then
            0
        else
            var v1, v2 := s1[i-1] as int, s2[i-1] as int;
            square_positive_lemma(v1);
            square_positive_lemma(v2);
            var vv1, vv2 := v1 * v1, v2 * v2;
            l2norm_squared(s1, s2, i-1) + vv1 + vv2
    }
}

