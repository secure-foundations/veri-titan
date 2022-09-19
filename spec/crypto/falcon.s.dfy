include "mq_poly.s.dfy"
include "mq_norm.s.dfy"

abstract module falcon_s(MQ: ntt_param_s, MQP: mq_poly_s(MQ)) {
    import MQN = mq_norm_s(MQ)

    function bound(): nat

    function poly_mod_product(a: seq<MQ.elem>, b: seq<MQ.elem>): (p: seq<MQ.elem>)
    {
        MQP.poly_mod(MQP.poly_mul(a, b), MQP.n_ideal())
    }

    predicate falcon_verify(c0: seq<MQ.elem>, s2: seq<MQN.nelem>, h: seq<MQ.elem>)
        requires |c0| == |s2| == |h| == MQ.N.full;
    {
        var tt0 := MQN.denormalize_elems(s2);
        var tt1 := poly_mod_product(tt0, h);
        var tt2 := MQP.poly_sub(tt1, c0);
        var s1 := MQN.normalize_elems(tt2);
        MQN.l2norm_squared(s1, s2, MQ.N.full) < bound()
    }
}
