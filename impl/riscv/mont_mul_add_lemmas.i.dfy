include "rsa_ops.i.dfy"

module mont_mul_add_lemmas {
  import opened bv_ops
  import opened rsa_ops
  import opened rv_machine

  import opened BASE_32_Seq
  import opened Mul
  import Power2
  import Power
  import opened DivMod

  lemma refine_uint64_view(lh: uint32, uh: uint32, full: uint64) returns (r: uint64_view_t)
    requires lh == uint64_lh(full);
    requires uh == uint64_uh(full);
    ensures valid_uint64_view(r, lh, uh)
  {
    r := uint64_cons(lh, uh, full);
    lemma_uint64_half_split(r.full);
    assert valid_uint64_view(r, lh, uh);
  }
  
  lemma uint64_view_zero() returns (r: uint64_view_t)
    ensures r == uint64_cons(0, 0, 0);
  {
    reveal uint64_lh();
    reveal uint64_uh();
    r := refine_uint64_view(0, 0, 0);
  }
  
  // predicate mont_mul_add_loop_inv(
  //   A: uint64_view_t,
  //   B: uint64_view_t,
  //   A_prev: uint64_view_t,
  //   B_prev: uint64_view_t,
  //   n: seq<uint32>,
  //   b: seq<uint32>,
  //   c: seq<uint32>,
  //   a: uint32,
  //   d0: uint32,
  //   i: nat)
  // {
  //   && |n| == |b| == |c|
  //   && 0 <= i < |n|

  //   && A.full == a * b[i] + c[i] + A_prev.uh
  //   && B.full == d0 * n[i] + A.lh + B_prev.uh
  //   && (i > 0 ==> c[i-1] == B.lh)
  // }

    predicate mont_loop_inv(
        xi: uint32,
        ui: uint32,
        p1: uint64_view_t,
        p2: uint64_view_t,
        y: seq<uint32>,
        m: seq<uint32>,
        prev_a: seq<uint32>,
        next_a: seq<uint32>,
        j: nat)
    {
        && |m| == |next_a| == |y| == |prev_a| == NUM_WORDS
        && (1 <= j <= NUM_WORDS)
        && (xi * to_nat(y[..j]) + ui * to_nat(m[..j]) + to_nat(prev_a[..j]) 
            == 
        to_nat([0] + next_a[..j-1]) + p2.uh * pow_B32(j) + p1.uh * pow_B32(j))
    }

    lemma mont_loop_inv_pre_lemma(
        xi: uint32, // a
        ui: uint32, //d0
        m0d: uint32, //d0inv
        p1: uint64_view_t, // A
        p2: uint64_view_t, // B
        y: seq<uint32>, // b
        m: seq<uint32>, // n
        a: seq<uint32>) // c
        requires |m| == |a| == |y| == NUM_WORDS;
        requires p1.full == xi * y[0] + a[0]; // A
        requires p2.full == ui * m[0] + p1.lh; // B == d0 * n[0] + A.lh
        requires cong_B32(m0d * to_nat(m), -1);
        requires p1.full == a[0] + y[0] * xi;
        requires ui == uint32_mul(p1.lh, m0d); 
        ensures mont_loop_inv(xi, ui, p1, p2, y, m, a, a, 1)
    // {
    //     assert cong_B32(ui, (a[0] + y[0] * xi) * m0d) by {
    //       calc ==> {
    //         ui == uint32_mul(p1.lh, m0d);
    //         {
    //           reveal uint64_lh();
    //         }
    //         cong_B32(ui, p1.lh * m0d);
    //         cong_B32(ui, uint64_lh(p1.full) * m0d);
    //         {
    //           reveal uint64_lh();
    //           LemmaMulModNoopLeftAuto();
    //         }
    //         cong_B32(ui, p1.full * m0d);
    //       }
    //     }

    //     assert cong_B32(m0d * m[0], -1) by {
    //         LemmaSeqLswModEquivalence(m);
    //         LemmaModMulEquivalent(to_nat(m), m[0], m0d, BASE_32);
    //         LemmaMulIsCommutativeAuto();
    //     }

    //     mont_loop_divisible_lemma(ui, m0d, p1, p2, m[0]);

    //     LemmaSeqLen1(y[..1]);
    //     LemmaSeqLen1(m[..1]);
    //     LemmaSeqLen1(a[..1]);

    //     assert p2.full == p2.uh * BASE_32 by {
    //         uint64_view_lemma(p2);
    //     }

    //     uint64_view_lemma(p1);

    //     calc {
    //         xi * to_nat(y[..1]) + ui * to_nat(m[..1]) + to_nat(a[..1]);
    //             { reveal Pow(); }
    //         p2.uh * pow_B32(1) + p1.uh * pow_B32(1);
    //             {
    //                 reveal ToNatRight();
    //                 assert to_nat([0]) == 0;
    //             }
    //         to_nat([0]) + p2.uh * pow_B32(1) + p1.uh * pow_B32(1);
    //             {
    //                 assert [0] + a[..0] == [0];
    //                 assert to_nat([0]) == to_nat([0] + a[..0]);
    //             }
    //         to_nat([0] + a[..0]) + p2.uh * pow_B32(1) + p1.uh * pow_B32(1);
    //     }
    // }

    lemma mont_loop_divisible_lemma(
        ui: int,
        m0d: int,
        p1: uint64_view_t,
        p2: uint64_view_t,
        m0: int)

        requires p2.full == ui * m0 + p1.lh;
        requires cong_B32(m0d * m0, -1);
        requires cong_B32(ui, p1.full * m0d);
        ensures p2.lh == 0;
    {
        var p1_full := p1.full as int;

        assert cong_B32(ui * m0, -p1_full) by {
            assert cong_B32(m0d * m0 * p1.full, -p1_full) by {
                LemmaModMulEquivalent(m0d * m0, -1, p1.full, BASE_32);
            }
            assert cong_B32(ui * m0, p1.full * m0d * m0) by {
                LemmaModMulEquivalentAuto();
            }
            assert p1.full * m0d * m0 == m0d * m0 * p1.full by {
                LemmaMulIsAssociativeAuto();
            }
        }

        calc ==> {
            cong_B32(ui * m0, -p1_full);
            cong_B32(ui * m0 + p1.lh , - p1_full + p1.lh);
                { lemma_uint64_half_split(p1.full); }
            cong_B32(ui * m0 + p1.lh, - (p1.uh as int * BASE_32 + p1.lh) + p1.lh);
            cong_B32(ui * m0 + p1.lh, - (p1.uh as int) * BASE_32);
                { assert cong_B32(- (p1.uh as int) * BASE_32, 0); }
            cong_B32(ui * m0 + p1.lh, 0);
        }

        calc ==> {
            p2.full == ui * m0 + p1.lh;
                { lemma_uint64_half_split(p2.full); }
            p2.lh + p2.uh * BASE_32 == ui * m0 + p1.lh;
            cong_B32(p2.lh + p2.uh * BASE_32, ui * m0 + p1.lh);
            cong_B32(ui * m0 + p1.lh, p2.lh + p2.uh * BASE_32);
            cong_B32(ui * m0 + p1.lh, p2.lh);
            cong_B32(p2.lh, 0);
        }

        assert cong_B32(p2.lh, 0);
    }
}
