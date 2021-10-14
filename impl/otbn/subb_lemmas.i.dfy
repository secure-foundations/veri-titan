include "rsa_ops.i.dfy"

module subb_lemmas {
    import opened bv_ops
    import opened ot_machine
    import opened ot_abstraction
    import opened rsa_ops

    import opened BASE_256_Seq

    predicate subb_inv(
        dst: seq<uint256>,
        carry: uint1,
        src1: seq<uint256>,
        src2: seq<uint256>,
        index: nat)
    requires |dst| == |src1| == |src2|;
    requires index <= |src1|;
    {
        (dst[..index], carry)
            == SeqSub(src1[..index], src2[..index])
    }

    lemma subb_inv_peri_lemma(
        dst: seq<uint256>,
        new_carry: uint1,
        src1: seq<uint256>,
        src2: seq<uint256>,
        old_carry: uint1,
        index: nat)

    requires |dst| == |src1| == |src2|;
    requires index < |src1|;
    requires subb_inv(dst, old_carry, src1, src2, index);
    requires (dst[index], new_carry)
        == uint256_subb(src1[index], src2[index], old_carry);
    ensures subb_inv(dst, new_carry, src1, src2, index + 1);
    {
        reveal SeqSub();
        var (zs, bin) := SeqSub(src1[..index], src2[..index]);
        var (z, bout) := uint256_subb(src1[index], src2[index], old_carry);

        assert dst[..index+1] == zs + [z];
        assert src1[..index+1] == src1[..index] + [src1[index]];
        assert src2[..index+1] == src2[..index] + [src2[index]];
    }

    lemma subb_inv_post_lemma(
        dst: seq<uint256>,
        carry: uint1,
        src1: seq<uint256>,
        src2: seq<uint256>)
        
    requires |dst| == |src1| == |src2|;
    requires subb_inv(dst, carry, src1, src2, |dst|);
    ensures ToNat(dst) == ToNat(src1) - ToNat(src2) + carry * pow_B256(|dst|);
    ensures carry == 0 <==> ToNat(src1) >= ToNat(src2)
    {
        var index := |dst|;
        assert dst[..index] == dst;
        assert src1[..index] == src1;
        assert src2[..index] == src2;
    
        LemmaSeqSub(src1, src2, dst, carry);

        assert ToNat(src1) - ToNat(src2) + carry * pow_B256(index) == ToNat(dst);

        LemmaSeqNatBound(dst);
    }
}