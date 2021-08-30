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

    function seq_subb(xs: seq<uint32>, ys: seq<uint32>) : (seq<uint32>, uint1)
        requires |xs| == |ys|
        ensures var (zs, bout) := seq_subb(xs, ys);
            && |zs| == |xs|
    {
        if |xs| == 0 then ([], 0)
        else
            var len' := |xs| - 1;
            var (zs, bin) := seq_subb(xs[..len'], ys[..len']);
            var (z, bout) := uint32_subb(xs[len'], ys[len'], bin);
            (zs + [z], bout)
    }

    lemma seq_subb_nat_lemma(xs: seq<uint32>, ys: seq<uint32>, zs: seq<uint32>, bout: uint1)
        requires |xs| == |ys|
        requires seq_subb(xs, ys) == (zs, bout);
        ensures to_nat(xs) - to_nat(ys) + bout * pow_B32(|xs|) == to_nat(zs)
    {
        reveal to_nat();
        if |xs| == 0 {
            reveal power();
        } else {
            var len' := |xs| - 1;
            var (zs', bin) := seq_subb(xs[..len'], ys[..len']);
            var (z, _) := uint32_subb(xs[len'], ys[len'], bin);
            assert bout * BASE_32 + xs[len'] - bin - ys[len'] == z;

            calc {
                to_nat(zs);
                to_nat(zs') + z * pow_B32(len');
                    { seq_subb_nat_lemma(xs[..len'], ys[..len'], zs', bin); }
                to_nat(xs[..len']) - to_nat(ys[..len']) + bin * pow_B32(len') + z * pow_B32(len');
                to_nat(xs[..len']) - to_nat(ys[..len']) + xs[len'] * pow_B32(len')
                    - ys[len'] * pow_B32(len') + bout * BASE_32 * pow_B32(len');
                    { reveal to_nat(); }
                to_nat(xs) - to_nat(ys) + bout * BASE_32 * pow_B32(len');
                    { reveal power(); }
                to_nat(xs) - to_nat(ys) + bout * pow_B32(|xs|);
            }
        }
    }

}
