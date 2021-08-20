include "../spec/rsa_ops.dfy"
include "../libraries/src/NonlinearArithmetic/DivMod.dfy"
include "../libraries/src/NonlinearArithmetic/Mul.dfy"
include "../libraries/src/NonlinearArithmetic/Power.dfy"

module mont_loop_lemmas {
    import opened bv_ops
    import opened vt_ops
    import opened rsa_ops
    import opened vt_consts
    import NT = NativeTypes
    import opened BASE_256_Seq
    import opened DivMod
    import opened Mul
    import opened Power

    lemma mont_loop_cong_lemma(
        p1: uint512_view_t,
        a0: uint256,
        y0: uint256,
        xi: uint256,
        w25: uint256,
        w26: uint256,
        m0d: uint256)

        requires a0 + y0 * xi == p1.full;
        requires ToNat([w25, w26]) == p1.lh * m0d;
        ensures cong_B256(w25, (a0 + y0 * xi) * m0d);
    {
        calc ==> {
            true;
            cong_B256(a0 + y0 * xi, p1.full);
                { uint512_view_lemma(p1); }
            cong_B256(a0 + y0 * xi, p1.lh + p1.uh * NT.BASE_256);
            cong_B256(a0 + y0 * xi, p1.lh);
            cong_B256(p1.lh, a0 + y0 * xi);
                { LemmaModMulEquivalentAuto(); }
            cong_B256(p1.lh * m0d, (a0 + y0 * xi) * m0d);
        }

        calc ==> {
            true;
                { LemmaSeqLen2([w25, w26]); }
            w25 + w26 * NT.BASE_256 == p1.lh * m0d;
            cong_B256(w25 + w26 * NT.BASE_256, p1.lh * m0d);
            cong_B256(w25 + w26 * NT.BASE_256, (a0 + y0 * xi) * m0d);
            cong_B256(w25, (a0 + y0 * xi) * m0d);
        }
    }

    lemma mont_loop_divisible_lemma(
        ui: int,
        m0d: int,
        p1: uint512_view_t,
        p2: uint512_view_t,
        m0: int)

        requires p2.full == ui * m0 + p1.lh;
        requires cong_B256(m0d * m0, -1);
        requires cong_B256(ui, p1.full * m0d);
        ensures p2.lh == 0;
    {
        var p1_full := p1.full as int;

        assert cong_B256(ui * m0, -p1_full) by {
            assert cong_B256(m0d * m0 * p1.full, -p1_full) by {
                LemmaModMulEquivalent(m0d * m0, -1, p1.full, NT.BASE_256);
            }
            assert cong_B256(ui * m0, p1.full * m0d * m0) by {
                LemmaModMulEquivalentAuto();
            }
            assert p1.full * m0d * m0 == m0d * m0 * p1.full by {
                LemmaMulIsAssociativeAuto();
            }
        }

        calc ==> {
            cong_B256(ui * m0, -p1_full);
            cong_B256(ui * m0 + p1.lh , - p1_full + p1.lh);
                { lemma_uint512_half_split(p1.full); }
            cong_B256(ui * m0 + p1.lh, - (p1.uh as int * NT.BASE_256 + p1.lh) + p1.lh);
            cong_B256(ui * m0 + p1.lh, - (p1.uh as int) * NT.BASE_256);
                { assert cong_B256(- (p1.uh as int) * NT.BASE_256, 0); }
            cong_B256(ui * m0 + p1.lh, 0);
        }

        assume false;

        calc ==> {
            p2.full == ui * m0 + p1.lh;
                { lemma_uint512_half_split(p2.full); }
            p2.lh + p2.uh * NT.BASE_256 == ui * m0 + p1.lh;
            cong_B256(p2.lh + p2.uh * NT.BASE_256, ui * m0 + p1.lh);
            cong_B256(ui * m0 + p1.lh, p2.lh + p2.uh * NT.BASE_256);
            cong_B256(ui * m0 + p1.lh, p2.lh);
            cong_B256(p2.lh, 0);
        }

        assert cong_B256(p2.lh, 0);
    }

    predicate mont_loop_inv(
        xi: uint256,
        ui: uint256,
        p1: uint512_view_t,
        p2: uint512_view_t,
        y: seq<uint256>,
        m: seq<uint256>,
        prev_a: seq<uint256>,
        next_a: seq<uint256>,
        j: nat)
    {
        && |m| == |next_a| == |y| == |prev_a| == NUM_WORDS
        && (1 <= j <= NUM_WORDS)
        && (xi * ToNat(y[..j]) + ui * ToNat(m[..j]) + ToNat(prev_a[..j]) 
            == 
        ToNat([0] + next_a[..j-1]) + p2.uh * pow_B256(j) + p1.uh * pow_B256(j))
    }

    lemma mont_loop_inv_pre_lemma(
        xi: uint256,
        ui: uint256,
        m0d: uint256,
        p1: uint512_view_t,
        p2: uint512_view_t,
        y: seq<uint256>,
        m: seq<uint256>,
        a: seq<uint256>)

        requires |m| == |a| == |y| == NUM_WORDS;
        requires p1.full == xi * y[0] + a[0];
        requires p2.full == ui * m[0] + p1.lh;
        requires cong_B256(m0d * ToNat(m), -1);
        requires cong_B256(ui, (a[0] + y[0] * xi) * m0d);

        ensures mont_loop_inv(xi, ui, p1, p2, y, m, a, a, 1)
    {
        assert cong_B256(m0d * m[0], -1) by {
            LemmaSeqLswModEquivalence(m);
            LemmaModMulEquivalent(ToNat(m), m[0], m0d, NT.BASE_256);
            LemmaMulIsCommutativeAuto();
        }

        mont_loop_divisible_lemma(ui, m0d, p1, p2, m[0]);

        LemmaSeqLen1(y[..1]);
        LemmaSeqLen1(m[..1]);
        LemmaSeqLen1(a[..1]);

        assert p2.full == p2.uh * NT.BASE_256 by {
            uint512_view_lemma(p2);
        }

        uint512_view_lemma(p1);

        calc {
            xi * ToNat(y[..1]) + ui * ToNat(m[..1]) + ToNat(a[..1]);
                { reveal Pow(); }
            p2.uh * pow_B256(1) + p1.uh * pow_B256(1);
                {
                    reveal ToNat();
                    assert ToNat([0]) == 0;
                }
            ToNat([0]) + p2.uh * pow_B256(1) + p1.uh * pow_B256(1);
                {
                    assert [0] + a[..0] == [0];
                    assert ToNat([0]) == ToNat([0] + a[..0]);
                }
            ToNat([0] + a[..0]) + p2.uh * pow_B256(1) + p1.uh * pow_B256(1);
        }
    }

    lemma mont_loop_inv_peri_lemma(
        xi: uint256,
        ui: uint256,
        p1: uint512_view_t,
        p2: uint512_view_t,
        next_p1: uint512_view_t,
        next_p2: uint512_view_t,
        y: seq<uint256>,
        m: seq<uint256>,
        prev_a: seq<uint256>,
        a: seq<uint256>,
        next_a: seq<uint256>,
        j: nat)

        requires 1 <= j < NUM_WORDS; // this is in the loop itself
        requires mont_loop_inv(xi, ui, p1, p2, y, m, prev_a, a, j);
        requires a[j] == prev_a[j];
        requires |next_a| == NUM_WORDS;
        requires next_p1.full == p1.uh + y[j] * xi + a[j];
        requires next_p2.full == m[j] * ui + next_p1.lh + p2.uh;
        requires next_a == a[j-1 := next_p2.lh];
        ensures mont_loop_inv(xi, ui, next_p1, next_p2, y, m, prev_a, next_a, j+1);
    {
        var y_nat := ToNat(y[..j]);
        var y_nat' := ToNat(y[..j+1]);
        var y_j := y[j];

        var m_nat := ToNat(m[..j]);
        var m_nat' := ToNat(m[..j+1]);
        var m_j := m[j];

        var ia_nat := ToNat(prev_a[..j]);
        var ia_nat' := ToNat(prev_a[..j+1]);
        var a_j := prev_a[j];

        var ea_nat := ToNat([0] + a[..j-1]);
        var ea_nat' := ToNat([0] + next_a[..j]);

        var pow_B256_j := pow_B256(j);
        var pow_B256_j' := pow_B256(j+1);

        var p1_uh := p1.uh;
        var p2_uh := p2.uh;

        assert pow_B256_j' == pow_B256_j * NT.BASE_256 by {
          reveal Pow();
        }

        assert xi * y_nat + ui * m_nat + ia_nat 
            == 
        ea_nat + p2_uh * pow_B256_j +p1_uh * pow_B256_j;

        assert p1_uh == next_p1.lh + next_p1.uh * NT.BASE_256 - y_j * xi - a_j by {
            uint512_view_lemma(next_p1);
        }

        assert p2_uh == next_p2.lh + next_p2.uh * NT.BASE_256 - m_j * ui - next_p1.lh by {
            uint512_view_lemma(next_p2);
        }

        assert ia_nat' == ia_nat + a_j * pow_B256_j by {
            assert prev_a[..j+1][..j] == prev_a[..j];
            LemmaToNatEqToNatRevAuto();
            reveal ToNatRev();
        }

        assert y_nat' == y_nat + y_j * pow_B256_j by {
            assert y[..j+1][..j] == y[..j];
            LemmaToNatEqToNatRevAuto();
            reveal ToNatRev();
        }

        assert m_nat' == m_nat + m_j * pow_B256_j by {
            assert m[..j+1][..j] == m[..j];
            LemmaToNatEqToNatRevAuto();
            reveal ToNatRev();
        }

        assert ea_nat' == ea_nat + next_p2.lh * pow_B256_j by {
            calc == {
                ToNat(next_a[..j]);
                    {
                        LemmaSeqPrefix(next_a[..j], j - 1);
                        assert next_a[..j-1] == next_a[..j][..j-1];
                        reveal ToNat();
                    }
                ToNat(next_a[..j-1]) + next_p2.lh * pow_B256(j-1);
                ToNat(a[..j-1]) + next_p2.lh * pow_B256(j-1);
            }

            assert ToNat([0] + a[..j-1]) == ToNat(a[..j-1]) * NT.BASE_256 by {
                reveal ToNat();
            }

            assert ToNat([0] + next_a[..j]) == ToNat(next_a[..j]) * NT.BASE_256 by {
                reveal ToNat();
            }

            assert pow_B256(j-1) * NT.BASE_256 == pow_B256(j) by {
                reveal Pow();
            }

            LemmaMulIsAssociativeAuto();
        }

        assert xi * y_nat' + ui * m_nat' + ia_nat'
            ==
        ea_nat' + next_p2.uh * pow_B256_j' + next_p1.uh * pow_B256_j' by {
            LemmaMulProperties();
        }
    }

    lemma mont_loop_inv_post_lemma(
        xi: uint256,
        ui: uint256,
        p1: uint512_view_t,
        p2: uint512_view_t,
        y: seq<uint256>,
        m: seq<uint256>,
        prev_a: seq<uint256>,
        a: seq<uint256>,
        bout: uint1)

        requires mont_loop_inv(xi, ui, p1, p2, y, m, prev_a, a, NUM_WORDS);
        requires uint256_addc(p1.uh, p2.uh, 0) == (a[NUM_WORDS-1], bout);

        ensures ToNat(a) * NT.BASE_256 + bout * pow_B256(NUM_WORDS+1)
            == xi * ToNat(y) + ui * ToNat(m) + ToNat(prev_a);
    {
        // var m := ToNat(m);
        calc {
            ToNat(a) * NT.BASE_256 + bout * pow_B256(NUM_WORDS+1);
                {
                    LemmaToNatEqToNatRev(a);
                    reveal ToNatRev();
                    LemmaToNatEqToNatRev(a[..NUM_WORDS-1]);
                }
            (ToNat(a[..NUM_WORDS-1]) + a[NUM_WORDS-1] * pow_B256(NUM_WORDS-1)) * NT.BASE_256 + bout * pow_B256(NUM_WORDS+1);
            ToNat(a[..NUM_WORDS-1]) * NT.BASE_256 + a[NUM_WORDS-1] * pow_B256(NUM_WORDS-1) * NT.BASE_256 + bout * pow_B256(NUM_WORDS+1);
                {
                    reveal Pow();
                    LemmaMulIsCommutativeAuto();
                    LemmaMulIsAssociativeAuto();
                }
            ToNat(a[..NUM_WORDS-1]) * NT.BASE_256 + a[NUM_WORDS-1] * pow_B256(NUM_WORDS) + bout * NT.BASE_256 * pow_B256(NUM_WORDS);
                { LemmaMulIsDistributiveAuto(); }
            ToNat(a[..NUM_WORDS-1]) * NT.BASE_256 + p2.uh * pow_B256(NUM_WORDS) + p1.uh * pow_B256(NUM_WORDS);
                { reveal ToNat(); }
            ToNat([0] + a[..NUM_WORDS-1]) + p2.uh * pow_B256(NUM_WORDS) + p1.uh * pow_B256(NUM_WORDS);
                {
                    assert y == y[..NUM_WORDS];
                    assert m == m[..NUM_WORDS];
                    assert prev_a == prev_a[..NUM_WORDS];
                }
            xi * ToNat(y) + ui * ToNat(m) + ToNat(prev_a);
        }
    }

    lemma mont_loop_cond_sub_borrow_lemma(xi: uint256,
        ui: uint256,
        y: seq<uint256>,
        m: nat,
        prev_a: nat,
        a: seq<uint256>,
        next_a: seq<uint256>,
        next_bout: uint1)

        requires m != 0;
        requires |next_a| == |y| == NUM_WORDS;
        requires prev_a < m + ToNat(y);
        requires ToNat(a) * NT.BASE_256 + pow_B256(NUM_WORDS+1)
            == xi * ToNat(y) + ui * m + prev_a;
        requires ToNat(next_a) - pow_B256(NUM_WORDS) * next_bout == ToNat(a) - m
        requires ToNat(a) + pow_B256(NUM_WORDS) < ToNat(y) + m

        ensures ToNat(next_a) < m + ToNat(y)
        ensures IsModEquivalent(ToNat(next_a) * NT.BASE_256, xi * ToNat(y) + ui * m + prev_a, m)
    {
        if ToNat(a) >= m {
            LemmaSeqNatBound(y);
            assert ToNat(a) + pow_B256(NUM_WORDS) < ToNat(y) + m;
            assert false; // prove by contradiction
        }
        if next_bout != 1 {
            LemmaSeqNatBound(next_a);
            assert false; // prove by contradiction
        }
        
        assert next_bout == 1;

        calc {
            ToNat(next_a) * NT.BASE_256;
            ToNat(a) * NT.BASE_256 + pow_B256(NUM_WORDS) * NT.BASE_256 - m * NT.BASE_256;
                { reveal Pow(); }
            ToNat(a) * NT.BASE_256 + pow_B256(NUM_WORDS+1) - m * NT.BASE_256;
            xi * ToNat(y) + ui * m + prev_a - m * NT.BASE_256;
        }
        
        calc ==> {
            true;
            IsModEquivalent(ToNat(next_a) * NT.BASE_256, xi * ToNat(y) + ui * m + prev_a - m * NT.BASE_256, m);
                { LemmaModMultiplesVanish(-1 * NT.BASE_256, xi * ToNat(y) + ui * m + prev_a, m); }
            IsModEquivalent(ToNat(next_a) * NT.BASE_256, xi * ToNat(y) + ui * m + prev_a, m);
        }
    }

    lemma mont_loop_cond_sub_lemma(
        xi: uint256,
        ui: uint256,
        y: seq<uint256>,
        m: nat,
        prev_a: nat,
        a: seq<uint256>,
        next_a: seq<uint256>,
        bout: uint1,
        next_bout: uint1)

        requires m != 0;
        requires |next_a| == |y| == NUM_WORDS;
        requires prev_a < m + ToNat(y);
        requires ToNat(a) * NT.BASE_256 + bout * pow_B256(NUM_WORDS+1)
            == xi * ToNat(y) + ui * m + prev_a;
        requires bout == 0 ==>
            ToNat(a) == ToNat(next_a)
        requires bout == 1 ==>
            ToNat(next_a) - pow_B256(NUM_WORDS) * next_bout == ToNat(a) - m

        ensures ToNat(next_a) < m + ToNat(y)
        ensures IsModEquivalent(ToNat(next_a) * NT.BASE_256, xi * ToNat(y) + ui * m + prev_a, m)
    {
        assert ToNat(a) + bout * pow_B256(NUM_WORDS) < ToNat(y) + m by {
            calc {
                (ToNat(a) + bout * pow_B256(NUM_WORDS)) * NT.BASE_256;
                ToNat(a) * NT.BASE_256 + bout * pow_B256(NUM_WORDS) * NT.BASE_256;
                    { reveal Pow(); }
                ToNat(a) * NT.BASE_256 + bout * pow_B256(NUM_WORDS+1);
                xi * ToNat(y) + ui * m + prev_a;
                <
                xi * ToNat(y) + ui * m + m + ToNat(y);
                    { LemmaMulIsDistributiveAuto(); }
                (xi + 1) * ToNat(y) + (ui + 1) * m;
                <=  {
                        assert xi + 1 <= NT.BASE_256;
                        assert ui + 1 <= NT.BASE_256;
                        LemmaMulInequalityConverseAuto();
                    }
                NT.BASE_256 * ToNat(y) + NT.BASE_256 * m;
                (ToNat(y) + m) * NT.BASE_256;
            }
        }
        
        if bout == 1 {
            mont_loop_cond_sub_borrow_lemma(xi, ui, y, m, prev_a, a, next_a, next_bout);
        }
    }

    predicate montmul_inv(
        a: seq<uint256>,
        x: seq<uint256>,
        i: nat,
        y: seq<uint256>,
        rsa: rsa_params)
    {
        && |a| == |y| == |x| == NUM_WORDS
        && i <= |x|
        && rsa_params_inv(rsa)
        && ToNat(a) < rsa.M + ToNat(y)
        && IsModEquivalent(ToNat(a) * pow_B256(i), ToNat(x[..i]) * ToNat(y), rsa.M)
    }

    lemma montmul_inv_lemma(
        prev_a: seq<uint256>,
        a: seq<uint256>,
        x: seq<uint256>, 
        i: nat,
        ui: int,
        y: seq<uint256>, 
        rsa: rsa_params)

        requires montmul_inv(prev_a, x, i, y, rsa);
        requires |a| == NUM_WORDS;
        requires i < |x|;
        requires ToNat(a) < rsa.M + ToNat(y);
        requires IsModEquivalent(ToNat(a) * pow_B256(1),
                x[i] * ToNat(y) + ui * rsa.M + ToNat(prev_a), rsa.M);
        ensures montmul_inv(a, x, i+1, y, rsa);
    {
        var curr_a := ToNat(a);
        var prev_a := ToNat(prev_a);
        calc ==> {
            IsModEquivalent(curr_a * pow_B256(1), x[i] * ToNat(y) + ui * rsa.M + prev_a, rsa.M);
                {
                    LemmaMulIsCommutativeAuto();
                    LemmaModMultiplesVanish(ui, x[i] * ToNat(y) + prev_a, rsa.M);
                }
            IsModEquivalent(curr_a * pow_B256(1), x[i] * ToNat(y) + prev_a, rsa.M);
                {
                    LemmaModMulEquivalent(curr_a * pow_B256(1), x[i] * ToNat(y) + prev_a, pow_B256(i), rsa.M);
                    LemmaMulIsDistributiveAuto();
                }
            IsModEquivalent(curr_a * pow_B256(1) * pow_B256(i), x[i] * ToNat(y) * pow_B256(i) + prev_a * pow_B256(i), rsa.M);
                {
                    reveal Pow();
                    LemmaMulIsAssociativeAuto();
                }
            IsModEquivalent(curr_a * pow_B256(1+i), x[i] * ToNat(y) * pow_B256(i) + prev_a * pow_B256(i), rsa.M);
                {
                    LemmaAddModNoopRight(x[i] * ToNat(y) * pow_B256(i), prev_a * pow_B256(i), rsa.M);
                    LemmaAddModNoopRight(x[i] * ToNat(y) * pow_B256(i), ToNat(x[..i]) * ToNat(y), rsa.M);
                }
            IsModEquivalent(curr_a * pow_B256(1+i), x[i] * ToNat(y) * pow_B256(i) + ToNat(x[..i]) * ToNat(y), rsa.M);
                { LemmaMulProperties(); }
            IsModEquivalent(curr_a * pow_B256(1+i), (x[i] * pow_B256(i) + ToNat(x[..i])) * ToNat(y), rsa.M);
                {
                    assert x[..i+1][..i] == x[..i];
                    LemmaToNatEqToNatRevAuto();
                    reveal ToNatRev();
                }
            IsModEquivalent(curr_a * pow_B256(1+i), ToNat(x[..i+1]) * ToNat(y), rsa.M);
        }

        assert IsModEquivalent(curr_a * pow_B256(1+i), ToNat(x[..i+1]) * ToNat(y), rsa.M);
    }
}