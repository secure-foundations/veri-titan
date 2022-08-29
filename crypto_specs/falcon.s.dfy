include "mq_poly.s.dfy"
include "mq_norm.s.dfy"

abstract module falcon_s(CMQ: ntt_param_s) {
    import MQP = mq_poly_s(CMQ)
    import MQN = mq_norm_s(CMQ)

	type elem = CMQ.elem
    type nelem = MQN.nelem
	type n_elems = CMQ.n_elems

	// const Q := CMQ.Q;
	const N := CMQ.N; 

    function bound(): nat

    predicate falcon_verify(c0: seq<elem>, s2: seq<nelem>, h: seq<elem>)
        requires |c0| == |s2| == |h| == N.full;
    {
        var tt0 := MQN.denormalize_nelems(s2);
        var tt1 := MQP.poly_mod(MQP.poly_mul(tt0, h), MQP.n_ideal());
        var tt2 := MQP.poly_sub(tt1, c0);
        var s1 := MQN.normalize_elems(tt2);
        MQN.l2norm_squared(s1, s2, N.full) < bound()
    }
}

module falcon_512_i refines falcon_s(ntt512_param_i)
{
    function bound(): nat {
        0x29845d6
    }
}