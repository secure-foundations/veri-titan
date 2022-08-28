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

    // -Q/2 <= e < Q/2 -> 0 <= e <= Q 
    function denormalize(e: nelem): MQ.elem
    {
        if e >= 0 then e else e + MQ.Q
    }

    lemma normalize_inverse(e: MQ.elem)
        ensures denormalize(normalize(e)) == e;
    {}

    lemma denormalize_inverse(e: nelem)
        ensures normalize(denormalize(e)) == e;
    {
        MQ.Nth_root_lemma();
    }
}

