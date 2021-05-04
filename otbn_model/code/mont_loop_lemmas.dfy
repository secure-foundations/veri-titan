include "../spec/vt_ops.dfy"

module mont_loop_lemmas {
    import opened bv_ops
    import opened vt_ops
    import opened vt_types
    import opened vt_consts
    import opened powers
    import opened congruences

    predicate mont_loop_inv(
        x_i: uint256,
        u_i: uint256,
        m_0': uint256,
        p_1: uint512_view_t,
        p_2: uint512_view_t,
        y: seq<uint256>,
        m: seq<uint256>,
        initial_a: seq<uint256>,
        a: seq<uint256>,
        j: nat)
    {
        && |m| == |a| == |y| == |initial_a| == NUM_WORDS;
        && (1 <= j <= NUM_WORDS)
        && (x_i * to_nat(y[..j]) + u_i * to_nat(m[..j]) + to_nat(initial_a[..j]) 
            == 
        to_nat([0] + a[..j-1]) + p_2.uh * pow_B256(j) + p_1.uh * pow_B256(j))
    }

    lemma mont_loop_divisible_lemma1
        (x_i: uint256,
        u_i: uint256,
        m_0': uint256,
        p_1: uint512_view_t,
        p_2: uint512_view_t,
        y_0: uint256,
        m_0: uint256,
        a_0: uint256)

        requires p_1.full == x_i * y_0 + a_0;
        requires p_2.full == u_i * m_0 + p_1.lh;
        requires cong_B256(m_0' * m_0, BASE_256 - 1);
        requires cong_B256(u_i, (a_0 + y_0 * x_i) * m_0');
        ensures p_2.lh == 0;
    {
        assume false; // TODO
    }

    lemma mont_loop_inv_lemma1(
        x_i: uint256,
        u_i: uint256,
        m_0': uint256,
        p_1: uint512_view_t,
        p_2: uint512_view_t,
        y: seq<uint256>,
        m: seq<uint256>,
        a: seq<uint256>)

        requires |m| == |a| == |y| == NUM_WORDS;
        requires cong_B256(m_0' * m[0], BASE_256 - 1);
        requires p_1.full == x_i * y[0] + a[0];
        requires p_2.full == u_i * m[0] + p_1.lh;
        requires cong_B256(m_0' * m[0], BASE_256 - 1);
        requires cong_B256(u_i, (a[0] + y[0] * x_i) * m_0');

        ensures mont_loop_inv(x_i, u_i, m_0', p_1, p_2, y, m, a, a, 1)
        {
            mont_loop_divisible_lemma1(x_i, u_i, m_0', p_1, p_2, y[0], m[0], a[0]);

            to_nat_lemma1(y[..1]);
            to_nat_lemma1(m[..1]);
            to_nat_lemma1(a[..1]);

            assert p_2.full == p_2.uh * BASE_256 by {
                uint512_view_lemma(p_2);
            }

            uint512_view_lemma(p_1);

            calc == {
                x_i * to_nat(y[..1]) + u_i * to_nat(m[..1]) + to_nat(a[..1]);
                p_2.uh * pow_B256(1) + p_1.uh * pow_B256(1);
                {
                    assert to_nat([0]) == 0 by {
                        reveal to_nat();
                    }
                }
                to_nat([0]) + p_2.uh * pow_B256(1) + p_1.uh * pow_B256(1);
                {
                    assert [0] + a[..0] == [0];
                }
                to_nat([0] + a[..0]) + p_2.uh * pow_B256(1) + p_1.uh * pow_B256(1);
            }
        }
}