include "falcon.s.dfy"
include "mq_ntt.i.dfy"
include "mq_poly.i.dfy"

module falcon_512_i refines
    falcon_s(ntt512_param_i, mq_poly_i(ntt512_param_i))
{
    import CMQ = ntt512_param_i
    import CMQP = mq_poly_i(CMQ)
    import CPV = poly_view_i(CMQ)

    import FNTT = mq_fntt_i(CMQ, CMQP, CPV)
    import INTT = mq_intt_i(CMQ, CMQP, CPV)

    function bound(): nat {
        0x29845d6
    }
}