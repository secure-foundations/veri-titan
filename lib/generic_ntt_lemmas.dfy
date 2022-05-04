include "generic_bv_ops.dfy"

abstract module generic_ntt_lemmas {
  
    import opened GBV: generic_bv_ops

    import opened Mul
    import opened Power
    import opened DivMod
    import opened integers

    type uint = GBV.BVSEQ.uint

    const NTT_PRIME: nat // the prime modulus for NTT, Falcon, etc.
}
