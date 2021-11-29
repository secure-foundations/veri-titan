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
  
    datatype mma_vars = mma_vars(
        frame_ptr: uint32, // writable
        iter_a: iter_t,
        a_i: uint32,
        i: nat,
        // d0: uint32,
        iter_b: iter_t,
        iter_c: iter_t, // writable
        iter_n: iter_t
    )

    predicate mma_vars_inv(
        vars: mma_vars,
        mem: mem_t,
        n_ptr: int, n_idx: int,
        c_ptr: int, c_idx: int,
        b_ptr: int, b_idx: int,
        rsa: rsa_params)
    {
        && valid_frame_ptr(mem, vars.frame_ptr, 12)

        && mvar_iter_inv(mem, vars.iter_a, -1, vars.i, NA)
        && vars.i <= NUM_WORDS
        && (vars.i < NUM_WORDS ==> vars.iter_a.buff[vars.i] == vars.a_i)
        && mvar_iter_inv(mem, vars.iter_n, n_ptr, n_idx, rsa.M)
        && mvar_iter_inv(mem, vars.iter_c, c_ptr, c_idx, NA)
        && mvar_iter_inv(mem, vars.iter_b, b_ptr, b_idx, NA)

        && vars.iter_c.base_addr != vars.iter_a.base_addr
        && vars.iter_c.base_addr != vars.iter_n.base_addr
        && vars.iter_c.base_addr != vars.iter_b.base_addr
        && vars.iter_c.base_addr != vars.frame_ptr

        && vars.frame_ptr != vars.iter_a.base_addr
        && vars.frame_ptr != vars.iter_n.base_addr
        && vars.frame_ptr != vars.iter_b.base_addr

        && rsa_params_inv(rsa)
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
        old_a: seq<uint32>,
        next_a: seq<uint32>,
        j: nat)
    {
        && |m| == |next_a| == |y| == |old_a| == NUM_WORDS
        && (1 <= j <= NUM_WORDS)
        && old_a[j..] == next_a[j..]
        && (xi * to_nat(y[..j]) + ui * to_nat(m[..j]) + to_nat(old_a[..j]) 
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
        requires ui == uint32_mul(p1.lh, m0d); 
        ensures mont_loop_inv(xi, ui, p1, p2, y, m, a, a, 1)

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

    lemma mont_loop_inv_peri_lemma(
        xi: uint32,
        ui: uint32,
        p1: uint64_view_t,
        p2: uint64_view_t,
        next_p1: uint64_view_t,
        next_p2: uint64_view_t,
        y: seq<uint32>,
        m: seq<uint32>,
        old_a: seq<uint32>,
        a: seq<uint32>,
        next_a: seq<uint32>,
        j: nat)

        requires 1 <= j < NUM_WORDS; // this is in the loop itself
        requires mont_loop_inv(xi, ui, p1, p2, y, m, old_a, a, j);
        requires a[j] == old_a[j];
        requires |next_a| == NUM_WORDS;
        requires next_p1.full == p1.uh + xi * y[j]  + a[j];
        requires next_p2.full == ui * m[j] + next_p1.lh + p2.uh;
        requires next_a == a[j-1 := next_p2.lh];
        ensures mont_loop_inv(xi, ui, next_p1, next_p2, y, m, old_a, next_a, j+1);

    lemma mont_loop_inv_post_lemma(
        xi: uint32,
        ui: uint32,
        p1: uint64_view_t,
        p2: uint64_view_t,
        y: seq<uint32>,
        m: seq<uint32>,
        prev_a: seq<uint32>,
        a: seq<uint32>,
        bout: uint1)

        requires mont_loop_inv(xi, ui, p1, p2, y, m, prev_a, a, NUM_WORDS);
        requires uint32_addc(p1.uh, p2.uh, 0) == (a[NUM_WORDS-1], bout);

        ensures to_nat(a) * BASE_32 + bout * pow_B32(NUM_WORDS+1)
            == xi * to_nat(y) + ui * to_nat(m) + to_nat(prev_a);

    lemma mont_loop_cond_sub_lemma(
        xi: uint32,
        ui: uint32,
        y: seq<uint32>,
        m: seq<uint32>,
        prev_a: seq<uint32>,
        a: seq<uint32>,
        next_a: seq<uint32>,
        bout: uint1,
        next_bout: uint1)

        requires to_nat(m) != 0;
        requires |next_a| == |y| == NUM_WORDS;
        requires to_nat(prev_a) < to_nat(m) + to_nat(y);
        requires to_nat(a) * BASE_32 + bout * pow_B32(NUM_WORDS+1)
            == xi * to_nat(y) + ui * to_nat(m) + to_nat(prev_a);
        requires bout == 0 ==>
            to_nat(a) == to_nat(next_a)
        requires bout == 1 ==>
            to_nat(next_a) - pow_B32(NUM_WORDS) * next_bout == to_nat(a) - to_nat(m)

        ensures to_nat(next_a) < to_nat(m) + to_nat(y)
        ensures IsModEquivalent(to_nat(next_a) * BASE_32, xi * to_nat(y) + ui * to_nat(m) + to_nat(prev_a), to_nat(m))

    predicate montmul_inv(
        a: seq<uint32>,
        x: seq<uint32>,
        i: nat,
        y: seq<uint32>,
        rsa: rsa_params)
    {
        && |a| == |y| == |x| == NUM_WORDS
        && i <= |x|
        && rsa_params_inv(rsa)
        && to_nat(a) < rsa.M + to_nat(y)
        && IsModEquivalent(to_nat(a) * pow_B32(i), to_nat(x[..i]) * to_nat(y), rsa.M)
    }

    lemma montmul_inv_lemma(
        prev_a: seq<uint32>,
        a: seq<uint32>,
        x: seq<uint32>, 
        i: nat,
        ui: int,
        y: seq<uint32>,
        rsa: rsa_params)

        requires montmul_inv(prev_a, x, i, y, rsa);
        requires |a| == NUM_WORDS;
        requires i < |x|;
        requires to_nat(a) < rsa.M + to_nat(y);
        requires IsModEquivalent(to_nat(a) * BASE_32,
                x[i] * to_nat(y) + ui * rsa.M + to_nat(prev_a), rsa.M);
        ensures montmul_inv(a, x, i+1, y, rsa);


}
