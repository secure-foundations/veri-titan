include "rv_consts.dfy"
include "bv_ops.dfy"
include "rv_ops.dfy"
include "../lib/powers.dfy"
include "../lib/congruences.dfy"
include "../libraries/src/Collections/Sequences/LittleEndianNat.dfy"

module BASE_32_Seq refines LittleEndianNat {
    import opened rv_ops
    import opened bv_ops
    import opened rv_consts
    
    function method BASE(): nat { BASE_32 }
}

module rsa_ops {
    import opened rv_consts
    import opened bv_ops
    import opened rv_ops

    import opened DivMod
    import opened Power
    import opened BASE_32_Seq
    import opened Seq

    /* to_nat definions & lemmas */

     lemma to_nat_lemma_0(xs: seq<uint32>)
         requires |xs| == 1
         ensures ToNatRight(xs) == xs[0]
     {
         reveal ToNatRight();
         assert BASE() == 0x1_00000000;
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
// 
//     lemma seq_subb_nat_lemma(xs: seq<uint32>, ys: seq<uint32>, zs: seq<uint32>, bout: uint1)
//         requires |xs| == |ys|
//         requires seq_subb(xs, ys) == (zs, bout);
//         ensures ToNatRight(xs) - ToNatRight(ys) + bout * pow_B32(|xs|) == ToNatRight(zs)
//     {
//         reveal ToNatRight();
//         if |xs| == 0 {
//             reveal power();
//         } else {
//             var len' := |xs| - 1;
//             var (zs', bin) := seq_subb(xs[..len'], ys[..len']);
//             var (z, _) := uint32_subb(xs[len'], ys[len'], bin);
//             assert bout * BASE_32 + xs[len'] - bin - ys[len'] == z;
// 
//             calc {
//                 ToNatRight(zs);
//                 ToNatRight(zs') + z * pow_B32(len');
//                     { seq_subb_nat_lemma(xs[..len'], ys[..len'], zs', bin); }
//                 ToNatRight(xs[..len']) - ToNatRight(ys[..len']) + bin * pow_B32(len') + z * pow_B32(len');
//                 ToNatRight(xs[..len']) - ToNatRight(ys[..len']) + xs[len'] * pow_B32(len')
//                     - ys[len'] * pow_B32(len') + bout * BASE_32 * pow_B32(len');
//                     { reveal ToNatRight(); }
//                 ToNatRight(xs) - ToNatRight(ys) + bout * BASE_32 * pow_B32(len');
//                     { reveal power(); }
//                 ToNatRight(xs) - ToNatRight(ys) + bout * pow_B32(|xs|);
//             }
//         }
//     }

}
