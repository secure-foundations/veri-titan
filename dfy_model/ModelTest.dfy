include "BitVector.dfy"
include "../otbn_model/lib/powers.dfy"
include "../otbn_model/lib/congruences.dfy"

module ModelTest {
    import opened CutomBitVector

    method simple(x: cbv)
        requires |x| == 768;
    {
        var r1: cbv := cbv_slice(x, 0, 385);
        var q1: cbv := cbv_lsr(x, 383);
    }

    method Main()
    {
        var a := from_nat(18);
        cbv_print(a);
        var v := to_nat(a);
        print v, "\n";
    }
}
