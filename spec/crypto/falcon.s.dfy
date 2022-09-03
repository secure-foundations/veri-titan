include "mq_poly.s.dfy"
include "mq_norm.s.dfy"

abstract module falcon_s(MQ: ntt_param_s, MQP: mq_poly_s(MQ)) {
    import MQN = mq_norm_s(MQ)

    type elem = MQ.elem
    type n_elems = MQ.n_elems
    type nelem = MQN.nelem

    const Q := MQ.Q;
    const N := MQ.N; 

    function bound(): nat

    predicate falcon_verify(c0: seq<elem>, s2: seq<nelem>, h: seq<elem>)
        requires |c0| == |s2| == |h| == N.full;
    {
        var tt0 := MQN.denormalize_n_elems(s2);
        var tt1 := MQP.poly_mod(MQP.poly_mul(tt0, h), MQP.n_ideal());
        var tt2 := MQP.poly_sub(tt1, c0);
        var s1 := MQN.normalize_elems(tt2);
        MQN.l2norm_squared(s1, s2, N.full) < bound()
    }
}
