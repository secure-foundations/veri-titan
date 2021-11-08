include "../dafny/generic_dw_add.i.dfy"
include "../../arch/otbn/abstraction.i.dfy"
include "../../lib/bv256_ops.dfy"

module bv256_dw_add refines generic_dw_add {
    import opened GBV = bv256_ops
    // import opened BVSEQ = GBV.BVSEQ
}