include "../spec/vt_ops.dfy"
include "mont_loop_lemmas.dfy"

module montmul_lemmas {
    import opened bv_ops
    import opened vt_ops
    import opened vt_types
    import opened vt_consts
    import opened powers
    import opened congruences
    import opened mont_loop_lemmas

    lemma montmul_inv_lemma_0(
        a: seq<uint256>,
        x: seq<uint256>, 
        i: nat,
        y: seq<uint256>, 
        key: pub_key)

        requires |a| == |x| == |y| == NUM_WORDS;
        requires to_nat(a) == 0;
        requires pub_key_inv(key);
        requires i == 0;
        
        ensures montmul_inv(a, x, i, y, key);
    {
        assert to_nat(x[..i]) == 0 by {
            reveal to_nat();
        }
        reveal cong();
        assert montmul_inv(a, x, i, y, key);
    }
}