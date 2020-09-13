include "NativeTypes.dfy"
include "../otbn_model/lib/powers.dfy"
include "../otbn_model/lib/congruences.dfy"

module barret384 {
    import opened NativeTypes
    import opened powers
    import opened congruences

 	const BASE :int := power(2, 256);

    method mul384(w9: uint256, w8: uint256, w11: uint256, w10: uint256)
        returns (w18: uint256, w17: uint256, w16: uint256)
        ensures (w9 * BASE + w8) * (w11 * BASE + w10) == 
            w18 * BASE * BASE + w17 * BASE + w16;


}