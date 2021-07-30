include "rv_consts.dfy"
include "bv_ops.dfy"
include "rv_ops.dfy"
include "../lib/powers.dfy"
include "../lib/congruences.dfy"

module rsa_ops {
    import opened rv_consts
    import opened bv_ops
    import opened rv_ops
    import opened powers
    import opened congruences

    /* to_nat definions & lemmas */

    function {:opaque} to_nat(xs: seq<uint32>): nat
    {
        if |xs| == 0 then 0
        else
            var len' := |xs| - 1;
            to_nat(xs[..len']) + xs[len'] * pow_B32(len')
    }

    lemma to_nat_lemma_0(xs: seq<uint32>)
        requires |xs| == 1
        ensures to_nat(xs) == xs[0]
    {
        reveal to_nat();
        reveal power();
    }

    lemma to_nat_lemma_1(xs: seq<uint32>)
        requires |xs| == 2
        ensures to_nat(xs) == xs[0] + xs[1] * BASE_32
    {
        reveal to_nat();
        to_nat_lemma_0(xs[..1]);
        reveal power();
    }
}
