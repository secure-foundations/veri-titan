include "../spec/vt_ops.dfy"

module mont_loop_lemmas {
    import opened bv_ops
    import opened vt_ops
    import opened vt_types
    import opened vt_consts
    import opened powers
    import opened congruences

    lemma mont_loop_inv_lemma1(
        x_i: uint256,
        u_i: uint256,
        p_1: uint512_view_t,
        p_2: uint512_view_t,
        m: seq<uint256>,
        A: seq<uint256>, 
        y: seq<uint256>)

        requires |m| == |A| == |y| >= 1;
        requires p_1.full == x_i * y[0]  + A[0];
        requires p_2.full == u_i * m[0] + p_1.lh;
        requires p_2.lh == 0;

        ensures x_i * to_nat(y[..1]) + u_i * to_nat(m[..1]) + to_nat(A[..1])
                == 
            p_2.uh * pow_B256(1) + p_1.uh * pow_B256(1);
        {
            to_nat_lemma1(y[..1]);
            to_nat_lemma1(m[..1]);
            to_nat_lemma1(A[..1]);

            assert p_2.full == p_2.uh * BASE_256 by {
                uint512_view_lemma(p_2);
            }

            uint512_view_lemma(p_1);
        }
}