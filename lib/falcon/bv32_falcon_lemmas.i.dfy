include "../../arch/riscv/machine.s.dfy"
include "../../arch/riscv/vale.i.dfy"
include "ct_std2rev_model.dfy"
include "../bv32_ops.dfy"

include "../DivModNeg.dfy"

module bv32_falcon_lemmas {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul
    import opened DivModNeg
    import opened integers
    import opened bv32_ops
    import opened rv_machine
    import opened rv_vale
    import opened mem
    import flat

	import opened pows_of_2
    import opened ntt_index
	import opened mq_polys
	import opened poly_view
    import opened nth_root
    import forward_ntt
    import inverse_ntt

    lemma {:axiom} rs1_is_half(a: uint32)
        ensures uint32_rs(a, 1) == a / 2;

    lemma {:axiom} ls1_is_double(a: uint32)
        requires a < BASE_31;
        ensures uint32_ls(a, 1) == a * 2;

    predicate {:opaque} buff_is_nsized(a: seq<uint16>)
    {
        && (|a| == N.full)
        && (forall i | 0 <= i < N.full :: a[i] < Q)
    }

    predicate fvar_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(iter, heap, if address >= 0 then address else iter.cur_ptr())
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && buff_is_nsized(iter.buff)
    }

    function {:opaque} buff_as_nsized(a: seq<uint16>): (a': n_sized)
        requires buff_is_nsized(a);
        ensures a == a';
    {
        reveal buff_is_nsized();
        a
    }

    function forward_lsize(view: forward_ntt.loop_view): (r: pow2_t)
        requires view.loop_view_wf();
        ensures r.full <= N.full
    {
        view.lsize()
    }

    predicate forward_ntt_eval_all(a: seq<uint16>, coeffs: seq<uint16>)
    {
        && buff_is_nsized(a)
        && buff_is_nsized(coeffs)
        && forward_ntt.ntt_eval_all(buff_as_nsized(a), buff_as_nsized(coeffs))
    }

    predicate forward_t_loop_inv(a: seq<uint16>, d: pow2_t, coeffs: seq<uint16>)
        requires 0 <= d.exp <= N.exp;
    {
        && buff_is_nsized(a)
        && buff_is_nsized(coeffs)
        && forward_ntt.t_loop_inv(buff_as_nsized(a), d, buff_as_nsized(coeffs))
    }

    lemma forward_t_loop_inv_pre_lemma(coeffs: seq<uint16>)
        requires buff_is_nsized(coeffs);
        ensures N.exp <= N.exp; // ??
        ensures forward_t_loop_inv(coeffs, N, coeffs);
    {
        forward_ntt.t_loop_inv_pre_lemma(buff_as_nsized(coeffs));
    }

    lemma forward_t_loop_inv_post_lemma(a: seq<uint16>, one: pow2_t, coeffs: seq<uint16>)
        requires one.exp == 0 <= N.exp;
        requires forward_t_loop_inv(a, one, coeffs);
        ensures forward_ntt_eval_all(a, coeffs);
    {
        forward_ntt.t_loop_inv_post_lemma(a, one, coeffs);
    }

    predicate forward_s_loop_inv(a: seq<uint16>, d: pow2_t, j: nat, bi: nat, view: forward_ntt.loop_view)
    {
        && buff_is_nsized(a)
        && view.s_loop_inv(buff_as_nsized(a), d, j, bi)
    }

    lemma forward_s_loop_inv_pre_lemma(
        a: seq<uint16>,
        d: pow2_t,
        j: nat,
        t: pow2_t,
        u: nat,
        ot3: uint32,
        t3: uint32,
        t6: uint32,
        s5: uint32,
        view: forward_ntt.loop_view)

        requires N == pow2_t_cons(512, 9);
        requires forward_j_loop_inv(a, d, j, u, view);
        requires t == view.lsize();
        requires j < view.lsize().full;
        requires t.full < BASE_32;
        requires s5 == uint32_ls(uint32_add(t.full, j), 1);
        requires t6 == 2 * d.full;
        requires ot3 == 2 * u;
        requires t3 == uint32_add(ot3, t6);

        ensures forward_s_loop_inv(a, d, j, 0, view);
        ensures s5 == (t.full + j) * 2; 
        ensures t.full + j < N.full;
        ensures t3 == 2 * u + 2 * d.full;
        ensures rev_mixed_powers_mont_table()[t.full + j] == 
            mqmul(rev_mixed_powers_mont_x_value(2 * j, d), R);
    {
        view.s_loop_inv_pre_lemma(buff_as_nsized(a), d, j);
        rev_mixed_powers_mont_table_lemma(t, d, j);
        assert uint32_add(t.full, j) == t.full + j;
        ls1_is_double(t.full + j);
        rev_mixed_powers_mont_table_lemma(t, d, j);

        assert u == j * (2 * d.full);
        assert d == view.hcount();

        calc {
            j * (2 * d.full) + d.full;
            <= 
            {
                LemmaMulInequality(j, 512, 2 * d.full);
            }
            512 * (2 * d.full) + d.full;
        }
    }

    lemma forward_s_loop_inv_post_lemma(
        a: seq<uint16>,
        d: pow2_t,
        j: nat,
        u: uint32,
        bi: nat,
        ot3: uint32,
        t3: uint32,
        t6: uint32,
        view: forward_ntt.loop_view)
    
        requires N == pow2_t_cons(512, 9);
        requires bi == d.full;
        requires t6 == 2 * d.full;
        requires u == j * (2 * d.full);
        requires forward_s_loop_inv(a, d, j, bi, view);
        requires ot3 == 2 * u + 2 * d.full;
        requires t3 == uint32_add(ot3, t6);
        ensures t3 == 2 * (u + 2 * d.full);
        ensures forward_j_loop_inv(a, d, j + 1, u + 2 * d.full, view);
    {
        view.s_loop_inv_post_lemma(buff_as_nsized(a), d, j, bi);

        assert u + 2 * d.full == (j + 1) * (2 * d.full) by {
            LemmaMulProperties();
        }

        calc == {
            ot3 + t6;
            2 * u + 2 * d.full + 2 * d.full;
            2 * (j * (2 * d.full)) + 2 * d.full + 2 * d.full;
            {
                LemmaMulProperties();
            }
            (2 * j + 2) * (2 * d.full);
        }

        assert d == view.hcount();

        calc {
            (2 * j + 2) * (2 * d.full);
            <= 
            {
                LemmaMulInequality(2 * j + 2, 1024, 2 * d.full);
            }
            1024 * (2 * d.full);
            <
            {
                assert d.full <= 512;
            }
            BASE_31;
        }
    }

    lemma forward_s_loop_index_lemma(
        a: seq<uint16>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s4: uint32,
        s2: uint32,
        t4: uint32,
        t5: uint32,
        t6: uint32,
        view: forward_ntt.loop_view)
        returns (s: nat)

        requires forward_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        requires s2 == 2 * bi + 2 * (j * (2 * d.full)); 
        requires flat.ptr_admissible_32(heap_b32_index_ptr(s4, N.full / 2 - 1));
        requires t4 == uint32_add(s4, s2);
        requires t5 == uint32_add(t4, t6);
        requires t6 == 2 * d.full;

        ensures s == bi + (2*j) * d.full;
        ensures t4 == s4 + 2 * s;
        ensures t5 == s4 + 2 * (s + d.full);
        ensures s + d.full < N.full;
        ensures a[s] == level_points_view(a, view.hsize)[bi][2*j];
        ensures s == point_view_index(bi, 2*j, view.hsize);
        ensures a[s+d.full] == level_points_view(a, view.hsize)[bi][2*j+1];
        ensures s+d.full == point_view_index(bi, 2*j+1, view.hsize);
    {
        s := view.higher_points_view_index_lemma(buff_as_nsized(a), d, j, bi);
        assert 2 * (bi + (2*j) * d.full) == 2 * bi + 2 * (j * (2 * d.full)) by {
            LemmaMulProperties();
        }
    }

    predicate forward_s_loop_update(
        a: seq<uint16>,
        a': seq<uint16>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: uint32,
        o: uint32,
        view: forward_ntt.loop_view)

        requires forward_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
    {
        && e < Q
        && o < Q
        && |a'| == |a|
        && s + d.full < |a|
        && a'[s + d.full] == o
        && a'[s] == e
        && a' == a[s + d.full := o][s := e]
        && assert buff_is_nsized(a') by {
            reveal buff_is_nsized();
        }
        && view.s_loop_update(buff_as_nsized(a), buff_as_nsized(a'), d, j, bi)
    }

    lemma forward_s_loop_inv_peri_lemma(a: seq<uint16>,
        a': seq<uint16>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: uint32,
        o: uint32,
        view: forward_ntt.loop_view)

        requires forward_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        requires forward_s_loop_update(a, a', d, j, bi, s, e, o, view);
        ensures forward_s_loop_inv(a', d, j, bi+1, view);
    {
        view.s_loop_inv_peri_lemma(a, a', d, j, bi);
        assert buff_is_nsized(a') by {
            reveal buff_is_nsized();
        }
    }

    lemma forward_higher_points_view_index_lemma(a: seq<uint16>, d: pow2_t, j: nat, bi: nat, view: forward_ntt.loop_view)
        returns (s: nat)
    
        requires forward_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        ensures s == bi + (2*j) * d.full;
        ensures s + d.full < N.full;
        ensures a[s] ==
            level_points_view(buff_as_nsized(a), view.hsize)[bi][2*j];
        ensures s == point_view_index(bi, 2*j, view.hsize);
        ensures a[s+d.full] ==
            level_points_view(buff_as_nsized(a), view.hsize)[bi][2*j+1];
        ensures s+d.full == point_view_index(bi, 2*j+1, view.hsize);
    {
        s := view.higher_points_view_index_lemma(buff_as_nsized(a), d, j, bi);
    }

    predicate forward_j_loop_inv(a: seq<uint16>, d: pow2_t, j: nat, u: nat, view: forward_ntt.loop_view)
    {
        && buff_is_nsized(a)
        && u == j * (2 * d.full)
        && view.j_loop_inv(buff_as_nsized(a), d, j)
    }

    lemma forward_j_loop_inv_pre_lemma(a: seq<uint16>, d: pow2_t, view: forward_ntt.loop_view)
        requires 0 <= d.exp < N.exp;
        requires forward_t_loop_inv(a, pow2_double(d), view.coefficients);
        requires view.loop_view_wf();
        requires view.hsize == block_size(d);
        ensures forward_j_loop_inv(a, d, 0, 0, view);
    {
        view.j_loop_inv_pre_lemma(buff_as_nsized(a), d);
    }

    lemma forward_j_loop_inv_post_lemma(a: seq<uint16>, d: pow2_t, j: nat, u: nat, view: forward_ntt.loop_view)
        requires forward_j_loop_inv(a, d, j, u, view);
        requires j == view.lsize().full;
        requires 0 <= view.hsize.exp <= N.exp;
        requires view.hsize == block_size(d);
        ensures forward_ntt.t_loop_inv(a, d, view.coefficients);
    {
        view.j_loop_inv_post_lemma(a, d, j);
    }

    function inverse_lsize(view: inverse_ntt.loop_view): (r: pow2_t)
        requires view.loop_view_wf();
        ensures r.full <= N.full
    {
        view.lsize()
    }

    predicate inverse_ntt_eval_all(a: seq<uint16>, coeffs: seq<uint16>)
    {
        && buff_is_nsized(a)
        && buff_is_nsized(coeffs)
        && inverse_ntt.ntt_eval_all(buff_as_nsized(a), buff_as_nsized(coeffs))
    }

    predicate inverse_t_loop_inv(a: seq<uint16>, d: pow2_t, coeffs: seq<uint16>)
        requires 0 <= d.exp <= N.exp;
    {
        && buff_is_nsized(a)
        && buff_is_nsized(coeffs)
        && inverse_ntt.t_loop_inv(buff_as_nsized(a), d, buff_as_nsized(coeffs))
    }

    lemma inverse_t_loop_inv_pre_lemma(coeffs: seq<uint16>)
        requires buff_is_nsized(coeffs);
        ensures N.exp <= N.exp; // ??
        ensures inverse_t_loop_inv(coeffs, N, coeffs);
    {
        inverse_ntt.t_loop_inv_pre_lemma(buff_as_nsized(coeffs));
    }

    lemma inverse_t_loop_inv_post_lemma(a: seq<uint16>, one: pow2_t, coeffs: seq<uint16>)
        requires one.exp == 0 <= N.exp;
        requires inverse_t_loop_inv(a, one, coeffs);
        ensures inverse_ntt_eval_all(a, coeffs);
    {
        inverse_ntt.t_loop_inv_post_lemma(a, one, coeffs);
    }

    predicate inverse_s_loop_inv(a: seq<uint16>, d: pow2_t, j: nat, bi: nat, view: inverse_ntt.loop_view)
    {
        && buff_is_nsized(a)
        && view.s_loop_inv(buff_as_nsized(a), d, j, bi)
    }

    lemma inverse_s_loop_inv_pre_lemma(
        a: seq<uint16>,
        d: pow2_t,
        j: nat,
        t: pow2_t,
        u: nat,
        ot3: uint32,
        t3: uint32,
        t6: uint32,
        s5: uint32,
        view: inverse_ntt.loop_view)

        requires N == pow2_t_cons(512, 9);
        requires inverse_j_loop_inv(a, d, j, u, view);
        requires t == view.lsize();
        requires j < view.lsize().full;
        requires t.full < BASE_32;
        requires s5 == uint32_ls(uint32_add(t.full, j), 1);
        requires t6 == 2 * d.full;
        requires ot3 == 2 * u;
        requires t3 == uint32_add(ot3, t6);

        ensures inverse_s_loop_inv(a, d, j, 0, view);
        ensures s5 == (t.full + j) * 2; 
        ensures t.full + j < N.full;
        ensures t3 == 2 * u + 2 * d.full;
        ensures rev_omega_inv_powers_mont_table()[t.full + j] == 
            mqmul(rev_omega_inv_powers_x_value(2 * j, d), R);
    {
        view.s_loop_inv_pre_lemma(buff_as_nsized(a), d, j);
        rev_omega_inv_powers_mont_table_lemma(t, d, j);
        assert uint32_add(t.full, j) == t.full + j;
        ls1_is_double(t.full + j);
        // rev_omega_inv_powers_mont_table_lemma(t, d, j);

        assert u == j * (2 * d.full);
        assert d == view.hcount();

        calc {
            j * (2 * d.full) + d.full;
            <= 
            {
                LemmaMulInequality(j, 512, 2 * d.full);
            }
            512 * (2 * d.full) + d.full;
        }
    }

    lemma inverse_s_loop_inv_post_lemma(
        a: seq<uint16>,
        d: pow2_t,
        j: nat,
        u: uint32,
        bi: nat,
        ot3: uint32,
        t3: uint32,
        t6: uint32,
        view: inverse_ntt.loop_view)
    
        requires N == pow2_t_cons(512, 9);
        requires bi == d.full;
        requires t6 == 2 * d.full;
        requires u == j * (2 * d.full);
        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires ot3 == 2 * u + 2 * d.full;
        requires t3 == uint32_add(ot3, t6);
        ensures t3 == 2 * (u + 2 * d.full);
        ensures inverse_j_loop_inv(a, d, j + 1, u + 2 * d.full, view);
    {
        view.s_loop_inv_post_lemma(buff_as_nsized(a), d, j, bi);

        assert u + 2 * d.full == (j + 1) * (2 * d.full) by {
            LemmaMulProperties();
        }

        calc == {
            ot3 + t6;
            2 * u + 2 * d.full + 2 * d.full;
            2 * (j * (2 * d.full)) + 2 * d.full + 2 * d.full;
            {
                LemmaMulProperties();
            }
            (2 * j + 2) * (2 * d.full);
        }

        assert d == view.hcount();

        calc {
            (2 * j + 2) * (2 * d.full);
            <= 
            {
                LemmaMulInequality(2 * j + 2, 1024, 2 * d.full);
            }
            1024 * (2 * d.full);
            <
            {
                assert d.full <= 512;
            }
            BASE_31;
        }
    }

    lemma inverse_s_loop_index_lemma(
        a: seq<uint16>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s4: uint32,
        s2: uint32,
        t4: uint32,
        t5: uint32,
        t6: uint32,
        view: inverse_ntt.loop_view)
        returns (s: nat)

        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        requires s2 == 2 * bi + 2 * (j * (2 * d.full)); 
        requires flat.ptr_admissible_32(heap_b32_index_ptr(s4, N.full / 2 - 1));
        requires t4 == uint32_add(s4, s2);
        requires t5 == uint32_add(t4, t6);
        requires t6 == 2 * d.full;

        ensures s == bi + (2*j) * d.full;
        ensures t4 == s4 + 2 * s;
        ensures t5 == s4 + 2 * (s + d.full);
        ensures s + d.full < N.full;
        ensures a[s] == level_points_view(a, view.hsize)[bi][2*j];
        ensures s == point_view_index(bi, 2*j, view.hsize);
        ensures a[s+d.full] == level_points_view(a, view.hsize)[bi][2*j+1];
        ensures s+d.full == point_view_index(bi, 2*j+1, view.hsize);
    {
        s := view.higher_points_view_index_lemma(buff_as_nsized(a), d, j, bi);
        assert 2 * (bi + (2*j) * d.full) == 2 * bi + 2 * (j * (2 * d.full)) by {
            LemmaMulProperties();
        }
    }

    predicate inverse_s_loop_update(
        a: seq<uint16>,
        a': seq<uint16>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: uint32,
        o: uint32,
        view: inverse_ntt.loop_view)

        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
    {
        && e < Q
        && o < Q
        && |a'| == |a|
        && s + d.full < |a|
        && a'[s + d.full] == o
        && a'[s] == e
        && a' == a[s + d.full := o][s := e]
        && assert buff_is_nsized(a') by {
            reveal buff_is_nsized();
        }
        && view.s_loop_update(buff_as_nsized(a), buff_as_nsized(a'), d, j, bi)
    }

    lemma inverse_s_loop_inv_peri_lemma(a: seq<uint16>,
        a': seq<uint16>,
        d: pow2_t,
        j: nat,
        bi: nat,
        s: nat,
        e: uint32,
        o: uint32,
        view: inverse_ntt.loop_view)

        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        requires inverse_s_loop_update(a, a', d, j, bi, s, e, o, view);
        ensures inverse_s_loop_inv(a', d, j, bi+1, view);
    {
        view.s_loop_inv_peri_lemma(a, a', d, j, bi);
        assert buff_is_nsized(a') by {
            reveal buff_is_nsized();
        }
    }

    lemma inverse_higher_points_view_index_lemma(a: seq<uint16>, d: pow2_t, j: nat, bi: nat, view: inverse_ntt.loop_view)
        returns (s: nat)
    
        requires inverse_s_loop_inv(a, d, j, bi, view);
        requires bi < d.full
        ensures s == bi + (2*j) * d.full;
        ensures s + d.full < N.full;
        ensures a[s] ==
            level_points_view(buff_as_nsized(a), view.hsize)[bi][2*j];
        ensures s == point_view_index(bi, 2*j, view.hsize);
        ensures a[s+d.full] ==
            level_points_view(buff_as_nsized(a), view.hsize)[bi][2*j+1];
        ensures s+d.full == point_view_index(bi, 2*j+1, view.hsize);
    {
        s := view.higher_points_view_index_lemma(buff_as_nsized(a), d, j, bi);
    }

    predicate inverse_j_loop_inv(a: seq<uint16>, d: pow2_t, j: nat, u: nat, view: inverse_ntt.loop_view)
    {
        && buff_is_nsized(a)
        && u == j * (2 * d.full)
        && view.j_loop_inv(buff_as_nsized(a), d, j)
    }

    lemma inverse_j_loop_inv_pre_lemma(a: seq<uint16>, d: pow2_t, view: inverse_ntt.loop_view)
        requires 0 <= d.exp < N.exp;
        requires inverse_t_loop_inv(a, pow2_double(d), view.coefficients);
        requires view.loop_view_wf();
        requires view.hsize == block_size(d);
        ensures inverse_j_loop_inv(a, d, 0, 0, view);
    {
        view.j_loop_inv_pre_lemma(buff_as_nsized(a), d);
    }

    lemma inverse_j_loop_inv_post_lemma(a: seq<uint16>, d: pow2_t, j: nat, u: nat, view: inverse_ntt.loop_view)
        requires inverse_j_loop_inv(a, d, j, u, view);
        requires j == view.lsize().full;
        requires 0 <= view.hsize.exp <= N.exp;
        requires view.hsize == block_size(d);
        ensures inverse_ntt.t_loop_inv(a, d, view.coefficients);
    {
        view.j_loop_inv_post_lemma(a, d, j);
    }

    lemma lemma_rs_by_31(x: int32)
      ensures x >= 0 ==> int32_rs(x, 31) == 0;
      ensures x < 0 ==> int32_rs(x, 31) == -1;
    {
      assert integers.BASE_31 == Power2.Pow2(31) by { Power2.Lemma2To64(); }

      if x >= 0 {
        assert x / Power2.Pow2(31) == 0 by {
          DivMod.LemmaBasicDivAuto();
        }
      } else {
        assert x / Power2.Pow2(31) == -1 by {
          DivModNeg.LemmaDivBounded(x, integers.BASE_31);
        }
      }
    }

    lemma lemma_mq_add_correct(d: uint32, b: uint32, c: uint32, r: uint32, x: uint32, y: uint32)
        requires 0 <= x < 12289;
        requires 0 <= y < 12289;
        requires d == uint32_add(x, uint32_add(y, to_uint32((-12289))));
        requires b == to_uint32(int32_rs(to_int32(d), 31));
        requires c == uint32_and(b, to_uint32(12289));
        requires r == uint32_add(c, d);
        ensures r == (x + y) % 12289;
    {
      var Q : int := 12289;

      // d == x + y - Q
      assert IsModEquivalent(d, x + y - Q, BASE_32);

      // -Q <= d < Q
      assert 0 <= x + y < 2*Q;
      assert (-Q) <= x + y - Q < Q;
      assert (-Q) <= to_int32(d) < Q;

      if to_int32(d) >= 0 {
        assert int32_rs(to_int32(d), 31) == 0 by { lemma_rs_by_31(to_int32(d)); }
        assert uint32_and(0, Q) == 0 by { reveal_and(); }
        assert IsModEquivalent(r, x + y, Q);
      }
      else {
        assert int32_rs(to_int32(d), 31) == -1 by { lemma_rs_by_31(to_int32(d)); }
        assert uint32_and(b, Q) == Q by { reveal_and(); }
        assert IsModEquivalent(r, x + y, Q);
      }

    } 

    lemma lemma_mq_sub_correct(d: uint32, b: uint32, c: uint32, r: uint32, x: int, y: int)
        requires 0 <= x < 12289;
        requires 0 <= y < 12289;
        requires d == uint32_sub(x, y);
        requires b == to_uint32(int32_rs(to_int32(d), 31));
        requires c == uint32_and(b, 12289);
        requires r == uint32_add(c, d);
        ensures r == (x - y) % 12289;
    {
      var Q : int := 12289;
      
      assert IsModEquivalent(d, x - y, BASE_32);
      assert -Q <= to_int32(d) < 2 * Q;
      
      if to_int32(d) >= 0 {
        assert int32_rs(to_int32(d), 31) == 0 by { lemma_rs_by_31(to_int32(d)); }
        assert uint32_and(b, Q) == 0 by { reveal_and(); }
        assert IsModEquivalent(r, x - y, Q);
      }
      else {
        assert int32_rs(to_int32(d), 31) == -1 by { lemma_rs_by_31(to_int32(d)); }
        assert uint32_and(b, Q) == Q by { reveal_and(); }
        assert IsModEquivalent(r, x - y, Q);
      }
    }

    lemma lemma_positive_rs(x: uint32, shift: nat)
      requires x >= 0;
      requires x < BASE_31;
      ensures to_uint32(int32_rs(x, shift)) == int32_rs(x, shift)
    {
      assert to_int32(x) == x;
      assert int32_rs(to_int32(x), shift) >= 0 by { DivMod.LemmaDivBasicsAuto(); }
    }

     lemma lemma_mq_rshift1_correct(par: uint32, b: uint32, c: uint32, d: uint32, r: uint32, x: int)
         requires 0 <= x < 12289;
         requires par == uint32_and(x, 1);
         requires b == uint32_sub(0, par);
         requires c == uint32_and(b, 12289);
         requires d == uint32_add(x, c);
         requires r == to_uint32(int32_rs(to_int32(d), 1));
 
         //ensures r == (x / 2) % 12289;
         ensures IsModEquivalent(2 * r, x, 12289);
         ensures r < 12289;
     {
       var Q : int := 12289;
       assert par == 0 || par == 1 by { reveal_and(); }
 
       if par == 0 {
         assert b == 0;
         assert c == 0 by { reveal_and(); }
         assert x % 2 == 0 by { reveal_and(); }
         assert d == x;
         
         assert 0 <= to_int32(d) < Q;
         assert r == int32_rs(to_int32(d), 1) by { lemma_positive_rs(x, 1); }
 
         assert r == d / Power2.Pow2(1);
         assert r == d / 2 by { Power2.Lemma2To64(); }
 
         assert IsModEquivalent(r, x / 2, Q);
         
       } else {
         assert b == 0xffff_ffff;
         assert c == Q by { reveal_and(); }
         assert d == uint32_add(x, Q);
         assert d == x + Q;

         assert 0 <= to_int32(d) <= x + Q;
         assert r == int32_rs(to_int32(d), 1) by { lemma_positive_rs(x + Q, 1); }
 
         assert IsModEquivalent(d, x, Q);
 
         assert r == d / Power2.Pow2(1);
         assert r == d / 2 by { Power2.Lemma2To64(); }
 
         assert r == (x + Q) / 2;
         
        //  assert x % 2 == 1 by { reveal_and(); }
        assume x % 2 == 1;
         assert Q % 2 == 1;
         assert (x + Q) % 2 == 0 by { DivMod.LemmaModAdds(x, Q, 2); }
 
         assert r == (x + Q) / 2;
         assert IsModEquivalent(2 * r, x + Q, Q);
       }
     }
}
