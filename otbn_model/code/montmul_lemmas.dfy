include "../spec/rsa_ops.dfy"
include "mont_loop_lemmas.dfy"

module montmul_lemmas {
    import opened bv_ops
    import opened vt_ops
    import opened rsa_ops
    import opened vt_consts
    import opened powers
    import opened congruences
    import opened mont_loop_lemmas

    function seq_zero(len: nat): (zs: seq<uint256>)
        ensures |zs| == len
    {
        if len == 0 then []
        else seq_zero(len - 1) + [0]
    }

    lemma seq_zero_to_nat_lemma(len: nat)
        ensures to_nat(seq_zero(len)) == 0
    {
        reveal to_nat();
    }

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