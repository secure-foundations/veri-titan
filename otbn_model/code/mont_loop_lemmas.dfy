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
        p_1: uint512_view_t,
        p_2: uint512_view_t,
        y: seq<uint256>,
        m: seq<uint256>,
        initial_a: seq<uint256>,
        a: seq<uint256>,
        j: nat)
    {
        && |m| == |a| == |y| == |initial_a| == NUM_WORDS
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
        requires cong_B256(u_i, p_1.full * m_0');
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

        ensures mont_loop_inv(x_i, u_i, p_1, p_2, y, m, a, a, 1)
    {
        mont_loop_divisible_lemma1(x_i, u_i, m_0', p_1, p_2, y[0], m[0], a[0]);

        to_nat_lemma1(y[..1]);
        to_nat_lemma1(m[..1]);
        to_nat_lemma1(a[..1]);

        assert p_2.full == p_2.uh * BASE_256 by {
            uint512_view_lemma(p_2);
        }

        uint512_view_lemma(p_1);

        calc {
            x_i * to_nat(y[..1]) + u_i * to_nat(m[..1]) + to_nat(a[..1]);
            p_2.uh * pow_B256(1) + p_1.uh * pow_B256(1);
                {
                    reveal to_nat();
                    assert to_nat([0]) == 0;
                }
            to_nat([0]) + p_2.uh * pow_B256(1) + p_1.uh * pow_B256(1);
                {
                    assert [0] + a[..0] == [0];
                }
            to_nat([0] + a[..0]) + p_2.uh * pow_B256(1) + p_1.uh * pow_B256(1);
        }
    }

    lemma mont_loop_inv_lemma2(
        x_i: uint256,
        u_i: uint256,
        p_1: uint512_view_t,
        p_2: uint512_view_t,
        next_p_1: uint512_view_t,
        next_p_2: uint512_view_t,
        y: seq<uint256>,
        m: seq<uint256>,
        initial_a: seq<uint256>,
        a: seq<uint256>,
        next_a: seq<uint256>,
        j: nat)

        requires 1 <= j < NUM_WORDS; // this is in the loop itself
        requires mont_loop_inv(x_i, u_i, p_1, p_2, y, m, initial_a, a, j);
        requires a[j] == initial_a[j];
        requires |next_a| == NUM_WORDS;
        requires next_p_1.full == p_1.uh + y[j] * x_i + a[j];
        requires next_p_2.full == m[j] * u_i + next_p_1.lh + p_2.uh;
        requires next_a == a[j-1 := next_p_2.lh];
        ensures mont_loop_inv(x_i, u_i, next_p_1, next_p_2, y, m, initial_a, next_a, j+1);
    {
        var y_nat := to_nat(y[..j]);
        var y_nat' := to_nat(y[..j+1]);
        var y_j := y[j];

        var m_nat := to_nat(m[..j]);
        var m_nat' := to_nat(m[..j+1]);
        var m_j := m[j];

        var ia_nat := to_nat(initial_a[..j]);
        var ia_nat' := to_nat(initial_a[..j+1]);
        var a_j := initial_a[j];

        var ea_nat := to_nat([0] + a[..j-1]);
        var ea_nat' := to_nat([0] + next_a[..j]);

        var pow_B256_j := pow_B256(j);
        var pow_B256_j' := pow_B256(j+1);

        var p1_uh := p_1.uh;
        var p2_uh := p_2.uh;

        assume pow_B256_j' == pow_B256_j * BASE_256;

        assert x_i * y_nat + u_i * m_nat + ia_nat 
            == 
        ea_nat + p2_uh * pow_B256_j +p1_uh * pow_B256_j;

        assert next_p_1.lh + next_p_1.uh * BASE_256 == p1_uh + y_j * x_i + a_j by {
            uint512_view_lemma(next_p_1);
        }

        assert next_p_2.lh + next_p_2.uh * BASE_256 == m_j * u_i + next_p_1.lh + p2_uh by {
            uint512_view_lemma(next_p_2);
        }

        assert ia_nat' == ia_nat + a_j * pow_B256_j by {
            assert initial_a[..j+1][..j] == initial_a[..j];
            reveal to_nat();
        }

        assert y_nat' == y_nat + y_j * pow_B256_j by {
            assert y[..j+1][..j] == y[..j];
            reveal to_nat();
        }

        assert m_nat' == m_nat + m_j * pow_B256_j by {
            assert m[..j+1][..j] == m[..j];
            reveal to_nat();
        }

        assert ea_nat' == ea_nat + next_p_2.lh * pow_B256_j by {
            calc == {
                to_nat(next_a[..j]);
                { to_nat_prefix_lemma(next_a, j); }
                to_nat(next_a[..j-1]) + next_p_2.lh * pow_B256(j-1);
                to_nat(a[..j-1]) + next_p_2.lh * pow_B256(j-1);
            }

            assert to_nat([0] + a[..j-1]) == to_nat(a[..j-1]) * BASE_256 by {
                to_nat_zero_prepend_lemma(a[..j-1]);
            }

            assert to_nat([0] + next_a[..j]) == to_nat(next_a[..j]) * BASE_256 by {
                to_nat_zero_prepend_lemma(next_a[..j]);
            }
            assume pow_B256(j-1) * BASE_256 == pow_B256(j);
        }

        assert x_i * y_nat' + u_i * m_nat' + ia_nat'
            == 
        ea_nat' + next_p_2.uh * pow_B256_j' + next_p_1.uh *pow_B256_j';
    }

    lemma mont_loop_inv_lemma3(
        x_i: uint256,
        u_i: uint256,
        p_1: uint512_view_t,
        p_2: uint512_view_t,
        y: seq<uint256>,
        m: seq<uint256>,
        initial_a: seq<uint256>,
        a: seq<uint256>,
        cout: uint1)

        requires mont_loop_inv(x_i, u_i, p_1, p_2, y, m, initial_a, a, NUM_WORDS);
        requires uint256_addc(p_1.uh, p_2.uh, 0) == (a[NUM_WORDS-1], cout);

        ensures to_nat(a) * BASE_256 + cout * pow_B256(NUM_WORDS+1)
            == x_i * to_nat(y) + u_i * to_nat(m) + to_nat(initial_a);
    {
        calc {
            // to_nat([0] + a) + cout * pow_B256(NUM_WORDS+1);
            //     { to_nat_zero_prepend_lemma(a); }
            to_nat(a) * BASE_256 + cout * pow_B256(NUM_WORDS+1);
                { reveal to_nat(); }
            (to_nat(a[..NUM_WORDS-1]) + a[NUM_WORDS-1] * pow_B256(NUM_WORDS-1)) * BASE_256 + cout * pow_B256(NUM_WORDS+1);
            to_nat(a[..NUM_WORDS-1]) * BASE_256 + a[NUM_WORDS-1] * pow_B256(NUM_WORDS-1) * BASE_256 + cout * pow_B256(NUM_WORDS+1);
                { reveal power(); }
            to_nat(a[..NUM_WORDS-1]) * BASE_256 + a[NUM_WORDS-1] * pow_B256(NUM_WORDS) + cout * pow_B256(NUM_WORDS+1);
                { reveal power(); }
            to_nat(a[..NUM_WORDS-1]) * BASE_256 + a[NUM_WORDS-1] * pow_B256(NUM_WORDS) + cout * BASE_256 * pow_B256(NUM_WORDS);
            to_nat(a[..NUM_WORDS-1]) * BASE_256 + p_2.uh * pow_B256(NUM_WORDS) + p_1.uh * pow_B256(NUM_WORDS);
                { to_nat_zero_prepend_lemma(a[..NUM_WORDS-1]); }
            to_nat([0] + a[..NUM_WORDS-1]) + p_2.uh * pow_B256(NUM_WORDS) + p_1.uh * pow_B256(NUM_WORDS);
                {
                    assert y == y[..NUM_WORDS];
                    assert m == m[..NUM_WORDS];
                    assert initial_a == initial_a[..NUM_WORDS];
                }
            x_i * to_nat(y) + u_i * to_nat(m) + to_nat(initial_a);
        }
    }

    lemma mont_loop_bound_lemma(
        x_i: uint256,
        u_i: uint256,
        y: seq<uint256>,
        m: seq<uint256>,
        initial_a: seq<uint256>,
        a: seq<uint256>,
        cout: uint1)

        requires |y| == NUM_WORDS;
        requires to_nat(initial_a) < to_nat(m) + to_nat(y);
        requires to_nat(a) * BASE_256 + cout * pow_B256(NUM_WORDS+1)
            == x_i * to_nat(y) + u_i * to_nat(m) + to_nat(initial_a);

        ensures to_nat(a) + cout * pow_B256(NUM_WORDS) < to_nat(y) + to_nat(m);
        ensures cout == 1 ==> to_nat(a) < to_nat(m);
    {
        calc {
            (to_nat(a) + cout * pow_B256(NUM_WORDS)) * BASE_256;
            to_nat(a) * BASE_256 + cout * pow_B256(NUM_WORDS) * BASE_256;
                { reveal power(); }
            to_nat(a) * BASE_256 + cout * pow_B256(NUM_WORDS+1);
            x_i * to_nat(y) + u_i * to_nat(m) + to_nat(initial_a);
        <
            x_i * to_nat(y) + u_i * to_nat(m) + to_nat(m) + to_nat(y);
            (x_i + 1) * to_nat(y) + (u_i + 1) * to_nat(m);
        <=
                {
                    assert x_i + 1 <= BASE_256;
                    assert u_i + 1 <= BASE_256;
                    assume false; // TODO
                }
            to_nat(y) * BASE_256 + to_nat(m) * BASE_256;
            (to_nat(y) + to_nat(m)) * BASE_256;
        }

        assert (to_nat(a) + cout * pow_B256(NUM_WORDS)) * BASE_256
            < (to_nat(y) + to_nat(m)) * BASE_256;

        assert to_nat(a) + cout * pow_B256(NUM_WORDS) < to_nat(y) + to_nat(m);

        if cout == 1 && to_nat(a) >= to_nat(m) {
            to_nat_bound_lemma(y);
            assert to_nat(a) + pow_B256(NUM_WORDS) < to_nat(y) + to_nat(m);
            assert false; // prove by contradiction
        }
    }

}