include "../Nonlinear_Arithmetic/DivMod.dfy"
include "../Nonlinear_Arithmetic/Mul.dfy"
include "../Nonlinear_Arithmetic/Power.dfy"
include "Seq.dfy"

abstract module NatSeq {

  import opened DivMod
  import opened Mul
  import opened Power
  import opened Seq

  function method BASE(): nat
		ensures BASE() > 1
  type uint = i: int | 0 <= i < BASE()

  //////////////////////////////////////////////////////////////////////////////
  //
  // to_nat definition and lemmas
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Converts a sequence to nat beginning from the lsw. */
  function method {:opaque} to_nat(xs: seq<uint>): nat
  {
    if |xs| == 0 then 0
    else
      lemma_mul_nonnegative_auto();
      to_nat(drop_first(xs)) * BASE() + first(xs)
  }

  /* Converts a sequence to nat beginning from the msw. */
  function method {:opaque} to_nat_rev(xs: seq<uint>): nat
  {
    if |xs| == 0 then 0
    else
      lemma_power_positive_auto();
      lemma_mul_nonnegative_auto();
      to_nat_rev(drop_last(xs)) + last(xs) * power(BASE(), |xs| - 1)
  }

  /* Given the same sequence, to_nat and to_nat_rev return the same value. */
  lemma lemma_to_nat_eq_to_nat_rev(xs: seq<uint>)
    ensures to_nat(xs) == to_nat_rev(xs)
  {
    reveal to_nat();
    reveal to_nat_rev();
    if xs != [] {
      if drop_last(xs) == [] {
        calc {
          to_nat_rev(xs);
          last(xs) * power(BASE(), |xs| - 1);
          { lemma_power_0_auto(); }
          to_nat(xs);
        }
      } else {
        calc {
          to_nat_rev(xs);
          to_nat_rev(drop_last(xs)) + last(xs) * power(BASE(), |xs| - 1);
          { lemma_to_nat_eq_to_nat_rev(drop_last(xs)); }
          to_nat(drop_last(xs)) + last(xs) * power(BASE(), |xs| - 1);
          to_nat(drop_first(drop_last(xs))) * BASE() + first(xs) + last(xs)
            * power(BASE(), |xs| - 1);
          { lemma_to_nat_eq_to_nat_rev(drop_first(drop_last(xs))); }
          to_nat_rev(drop_first(drop_last(xs))) * BASE() + first(xs) + last(xs)
            * power(BASE(), |xs| - 1);
          {
            assert drop_first(drop_last(xs)) == drop_last(drop_first(xs));
            reveal power();
            lemma_mul_properties();
          }
          to_nat_rev(drop_last(drop_first(xs))) * BASE() + first(xs) + last(xs)
            * power(BASE(), |xs| - 2) * BASE();
          { lemma_mul_is_distributive_add_other_way_auto(); }
          to_nat_rev(drop_first(xs)) * BASE() + first(xs);
          { lemma_to_nat_eq_to_nat_rev(drop_first(xs)); }
          to_nat(xs);
        }
      }
    }
  }

  lemma lemma_to_nat_eq_to_nat_rev_auto()
    ensures forall xs: seq<uint> {:trigger to_nat_rev(xs)}{:trigger to_nat(xs)}
      :: to_nat(xs) == to_nat_rev(xs)
  {
    reveal to_nat();
    reveal to_nat_rev();
    forall xs: seq<uint> {:trigger to_nat_rev(xs)}{:trigger to_nat(xs)}
      ensures to_nat(xs) == to_nat_rev(xs)
    {
      lemma_to_nat_eq_to_nat_rev(xs);
    }
  }

  /* Proves the nat representation of a sequence of length 1. */
  lemma lemma_seq_len_1(xs: seq<uint>)
    requires |xs| == 1
    ensures to_nat(xs) == first(xs)
  {
    reveal to_nat();
  }

  /* Proves the nat representation of a sequence of length 2. */
  lemma lemma_seq_len_2(xs: seq<uint>)
    requires |xs| == 2
    ensures to_nat(xs) == first(xs) + xs[1] * BASE()
  {
    reveal to_nat();
    lemma_seq_len_1(drop_last(xs));
  }

  /* Proves the nat representation of a sequence is bounded by BASE() to the
  power of the sequence length. */
  lemma lemma_seq_nat_bound(xs: seq<uint>)
    ensures to_nat(xs) == to_nat_rev(xs) < power(BASE(), |xs|)
  {
    reveal to_nat_rev();
    lemma_to_nat_eq_to_nat_rev_auto();
    reveal power();
    if |xs| != 0 {
      var len' := |xs| - 1;
      var pow := power(BASE(), len');
      calc {
        to_nat(xs);
        to_nat_rev(xs);
        to_nat_rev(drop_last(xs)) + last(xs) * pow;
        <  { lemma_seq_nat_bound(drop_last(xs)); }
        pow + last(xs) * pow;
        <= {
            lemma_power_positive_auto();
            lemma_mul_inequality_auto();
           }
        pow + (BASE() - 1) * pow;
           { lemma_mul_is_distributive_auto(); }
        power(BASE(), len' + 1);
      }
    }
  }

  /* Nat representation of a sequence based on its prefix. */
  lemma lemma_seq_prefix(xs: seq<uint>, i: nat)
    requires 0 <= i <= |xs|
    ensures to_nat(xs[..i]) + to_nat(xs[i..]) * power(BASE(), i) == to_nat(xs)
  {
    reveal to_nat();
    reveal power();
    if i == 1 {
      assert to_nat(xs[..1]) == first(xs);
    } else if i > 1 {
      calc {
        to_nat(xs[..i]) + to_nat(xs[i..]) * power(BASE(), i);
        to_nat(drop_first(xs[..i])) * BASE() + first(xs) + to_nat(xs[i..]) * power(BASE(), i);
          {
            assert drop_first(xs[..i]) == drop_first(xs)[..i-1];
            lemma_mul_properties();
          }
        to_nat(drop_first(xs)[..i-1]) * BASE() + first(xs) + (to_nat(xs[i..]) * power(BASE(), i - 1)) * BASE();
          { lemma_mul_is_distributive_add_other_way_auto(); }
        (to_nat(drop_first(xs)[..i-1]) + to_nat(drop_first(xs)[i-1..]) * power(BASE(), i - 1)) * BASE() + first(xs);
          { lemma_seq_prefix(drop_first(xs), i - 1); }
        to_nat(xs);
      }
    }
  }

  /* If there is an inequality between the most signficant words of two
  sequences, then there is an inequality between the nat representations of
  those sequences. */
  lemma lemma_seq_msw_inequality(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys| > 0
    requires last(xs) < last(ys)
    ensures to_nat(xs) < to_nat(ys)
  {
    reveal to_nat_rev();
    lemma_to_nat_eq_to_nat_rev_auto();
    var len' := |xs| - 1;
    calc {
      to_nat(xs);
      to_nat_rev(xs);
      <  { lemma_seq_nat_bound(drop_last(xs)); }
      power(BASE(), len') + last(xs) * power(BASE(), len');
      == { lemma_mul_is_distributive_auto(); }
      (1 + last(xs)) * power(BASE(), len');
      <= { lemma_power_positive_auto(); lemma_mul_inequality_auto(); }
      to_nat_rev(ys);
      to_nat(ys);
    }
  }

  /* If two sequence prefixes do not have the same nat representations, then the two sequences do not have the same nat representations. */
  lemma lemma_seq_prefix_neq(xs: seq<uint>, ys: seq<uint>, i: nat)
    requires 0 <= i <= |xs| == |ys|
    requires to_nat(xs[..i]) != to_nat(ys[..i])
    ensures to_nat(xs) != to_nat(ys)
    decreases |xs| - i
  {
    if i == |xs| {
      assert xs[..i] == xs;
      assert ys[..i] == ys;
    } else {
      if xs[i] == ys[i] {
        reveal to_nat_rev();
        assert drop_last(xs[..i+1]) == xs[..i];
        assert drop_last(ys[..i+1]) == ys[..i];

        lemma_to_nat_eq_to_nat_rev_auto();
        assert to_nat(xs[..i+1]) == to_nat_rev(xs[..i+1]);
      } else {
        if xs[i] < ys[i]  { lemma_seq_msw_inequality(xs[..i+1], ys[..i+1]); }
        else              { lemma_seq_msw_inequality(ys[..i+1], xs[..i+1]); }
      }
      lemma_seq_prefix_neq(xs, ys, i + 1);
    }
  }

  /* If two sequences are not equal, their nat representations are not equal. */
  lemma lemma_seq_neq(xs: seq<uint>, ys: seq<uint>, n: nat)
    requires |xs| == |ys| == n
    requires xs != ys
    ensures to_nat(xs) != to_nat(ys)
  {
    ghost var i: nat := 0;

    while i < n
      invariant 0 <= i < n
      invariant xs[..i] == ys[..i]
    {
      if xs[i] != ys[i] {
        break;
      }
      i := i + 1;
    }
    assert to_nat_rev(xs[..i]) == to_nat_rev(ys[..i]);

    reveal to_nat_rev();
    assert xs[..i+1][..i] == xs[..i];
    assert ys[..i+1][..i] == ys[..i];
    lemma_power_positive_auto();
    lemma_mul_strict_inequality_auto();
    assert to_nat_rev(xs[..i+1]) != to_nat_rev(ys[..i+1]);
    lemma_to_nat_eq_to_nat_rev_auto();

    lemma_seq_prefix_neq(xs, ys, i+1);
  }

  /* Proves mod equivalence between the nat representation of a sequence and
  the lsw of the sequence.*/
  lemma lemma_seq_lsw_mod_equivalence(xs: seq<uint>)
    requires |xs| >= 1;
    ensures is_mod_equivalent(to_nat(xs), first(xs), BASE());
  {
    if |xs| == 1 {
      lemma_seq_len_1(xs);
      lemma_mod_equivalence_auto();
    } else {
      assert is_mod_equivalent(to_nat(xs), first(xs), BASE()) by {
        reveal to_nat();
        calc ==> {
          true;
            { lemma_mod_equivalence_auto(); }
          is_mod_equivalent(to_nat(xs),
                            to_nat(drop_first(xs)) * BASE() + first(xs),
                            BASE());
            { lemma_mod_multiples_basic_auto(); }
          is_mod_equivalent(to_nat(xs), first(xs), BASE());
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // to_seq definition and lemmas
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Converts a nat to a sequence. */
  function method {:opaque} to_seq(n: nat): seq<uint>
  {
    if n == 0 then []
    else
      lemma_div_basics_auto();
      lemma_div_decreases_auto();
      [n % BASE()] + to_seq(n / BASE())
  }

  /* Converts a nat to a sequence of a specified length. */
  function method {:opaque} to_seq_with_len(n: nat, len: nat): (xs: seq<uint>)
    requires power(BASE(), len) > n
    ensures |xs| == len
  {
    reveal power();
    if n == 0 then
      (if len == 0 then []
       else
        lemma_power_positive(BASE(), len - 1);
        [0] + to_seq_with_len(n, len - 1))
    else
      lemma_div_basics_auto();
      lemma_div_decreases_auto();
      lemma_multiply_divide_lt_auto();
      [n % BASE()] + to_seq_with_len(n / BASE(), len - 1)
  }

  /* nat representation of an all zero sequence is 0. */
  lemma lemma_to_seq_with_len_zero(len: nat)
    ensures power(BASE(), len) > 0
    ensures to_nat(to_seq_with_len(0, len)) == 0
  {
    reveal to_nat();
    reveal to_seq_with_len();
    lemma_power_positive(BASE(), len);
    if len > 0 {
      calc {
        to_nat(to_seq_with_len(0, len));
        to_nat([0] + to_seq_with_len(0, len - 1));
        to_nat(to_seq_with_len(0, len - 1)) * BASE();
          {
            lemma_to_seq_with_len_zero(len - 1);
            lemma_mul_basics_auto();
          }
        0;
      }
    }
  }

  /* Proves that if we start with a nat, convert it to a sequence using to_seq
  and to_seq_with_len, and convert it back, the resulting numbers are
  equivalent. */
  lemma lemma_to_seq_with_len_eq_to_seq(n: nat, len: nat)
    requires power(BASE(), len) > n
    ensures to_nat(to_seq_with_len(n, len)) == to_nat(to_seq(n))
  {
    reveal to_nat();
    reveal to_seq_with_len();
    reveal to_seq();
    if n == 0 && len != 0 {
      lemma_to_seq_with_len_zero(len);
    } else if n > 0 {
      calc {
        to_nat(to_seq_with_len(n, len));
          {
            lemma_div_basics_auto();
            lemma_multiply_divide_lt_auto();
          }
        to_nat([n % BASE()] + to_seq_with_len(n / BASE(), len - 1));
        to_nat([n % BASE()]) + to_nat(to_seq_with_len(n / BASE(), len - 1)) * BASE();
          {
            lemma_div_decreases_auto();
            lemma_to_seq_with_len_eq_to_seq(n / BASE(), len - 1);
          }
        to_nat([n % BASE()]) + to_nat(to_seq(n / BASE())) * BASE();
        to_nat(to_seq(n));
      }
    }
  }

  /* Proves that if we start with a nat, convert it to a sequence, and convert
  it back, we get the same nat we started with. */
  lemma lemma_nat_seq_nat(n: nat)
    ensures to_nat(to_seq(n)) == n
    decreases n
  {
    reveal to_nat();
    reveal to_seq();
    if n > 0 {
      calc {
        to_nat(to_seq(n));
          { lemma_div_basics_auto(); }
        to_nat([n % BASE()] + to_seq(n / BASE()));
        n % BASE() + to_nat(to_seq(n / BASE())) * BASE();
          {
            lemma_div_decreases_auto();
            lemma_nat_seq_nat(n / BASE());
          }
        n % BASE() + n / BASE() * BASE();
          { lemma_fundamental_div_mod(n, BASE()); }
        n;
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Sequences with zeros
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Generates a sequence of zeros with length len. */
  function method {:opaque} seq_zero(len: nat): (zs: seq<uint>)
    ensures |zs| == len
  {
    if len == 0 then [] else [0] + seq_zero(len - 1)
  }

  /* nat representation of an all zero sequence is 0. */
  lemma lemma_seq_zero_nat(len: nat)
    ensures to_nat(seq_zero(len)) == 0
  {
    reveal to_nat();
    if len > 0 {
      calc {
        to_nat(seq_zero(len));
          { reveal seq_zero(); }
        to_nat([0] + seq_zero(len - 1));
        to_nat(seq_zero(len - 1)) * BASE() + 0;
          {
            lemma_seq_zero_nat(len - 1);
            lemma_mul_basics_auto();
          }
        0;
      }
    }
  }

  /* Prepending a zero is equal to multiplying the nat representation of the
  sequence by BASE(). */
  lemma lemma_seq_prepend_zero(xs: seq<uint>)
    ensures to_nat([0] + xs) == to_nat(xs) * BASE()
  {
    reveal to_nat();
  }

  /* Appending a zero does not change the nat representation of the sequence. */
  lemma lemma_seq_append_zero(xs: seq<uint>) 
    ensures to_nat(xs + [0]) == to_nat(xs)
  {
    reveal to_nat_rev();
    lemma_to_nat_eq_to_nat_rev_auto();
    calc == {
      to_nat(xs + [0]);
      to_nat_rev(xs + [0]);
      to_nat_rev(xs) + 0 * power(BASE(), |xs|);
        { lemma_mul_basics_auto(); }
      to_nat_rev(xs);
      to_nat(xs);
    }
  }

  /* Extend a sequence to a specified length. */
  function method {:opaque} seq_extend(xs: seq<uint>, n: nat): (ys: seq<uint>)
    requires |xs| <= n
    ensures |ys| == n
    decreases n - |xs|
  {
    if |xs| >= n then xs else seq_extend(xs + [0], n)
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Addition and subtraction
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Adds two sequences. */
  function method {:opaque} seq_add(xs: seq<uint>,
                                    ys: seq<uint>): (seq<uint>, nat)
    requires |xs| == |ys|
    ensures var (zs, cout) := seq_add(xs, ys); |zs| == |xs|
  {
    reveal seq_add();
    if |xs| == 0 then ([], 0)
    else
      var (zs', cin) := seq_add(drop_last(xs), drop_last(ys));
      var sum: int := last(xs) + last(ys) + cin;
      var (sum_out, cout) := if sum < BASE() then (sum, 0) else (sum - BASE(), 1);
      (zs' + [sum_out], cout)
  }

  /* Proves seq_add yields the same value as converting the sequences to nats,
  then adding them. */
  lemma lemma_seq_add_nat(xs: seq<uint>,
                          ys: seq<uint>,
                          zs: seq<uint>,
                          cout: nat)
    requires |xs| == |ys|
    requires seq_add(xs, ys) == (zs, cout)
    ensures to_nat(xs) + to_nat(ys) == to_nat(zs) + cout * power(BASE(), |xs|)
  {
    reveal seq_add();
    if |xs| == 0 {
      reveal to_nat();
    } else {
      var pow := power(BASE(), |xs| - 1);
      var (zs', cin) := seq_add(drop_last(xs), drop_last(ys));
      var sum: int := last(xs) + last(ys) + cin;
      var z := if sum < BASE() then sum else sum - BASE();
      assert sum == z + cout * BASE();

      reveal to_nat_rev();
      lemma_to_nat_eq_to_nat_rev_auto();
      calc {
        to_nat(zs);
        to_nat_rev(zs);
        to_nat_rev(zs') + z * pow;
          { lemma_seq_add_nat(drop_last(xs), drop_last(ys), zs', cin); }
        to_nat_rev(drop_last(xs)) + to_nat_rev(drop_last(ys)) - cin * pow + z * pow;
          {
            lemma_mul_equality_auto();
            assert sum * pow == (z + cout * BASE()) * pow;
            lemma_mul_is_distributive_auto();
          } 
        to_nat_rev(xs) + to_nat_rev(ys) - cout * BASE() * pow;
          {
            lemma_mul_is_associative(cout, BASE(), pow);
            reveal power();
          }
        to_nat_rev(xs) + to_nat_rev(ys) - cout * power(BASE(), |xs|);
        to_nat(xs) + to_nat(ys) - cout * power(BASE(), |xs|);
      }
    }
  }

  /* Subtracts two sequences. */
  function method {:opaque} seq_sub(xs: seq<uint>,
                                    ys: seq<uint>): (seq<uint>, nat)
    requires |xs| == |ys|
    ensures var (zs, cout) := seq_sub(xs, ys); |zs| == |xs|
  {
    reveal seq_sub();
    if |xs| == 0 then ([], 0)
    else 
      var (zs, cin) := seq_sub(drop_last(xs), drop_last(ys));
      var (diff_out, cout) := if last(xs) >= last(ys) + cin
                              then (last(xs) - last(ys) - cin, 0)
                              else (BASE() + last(xs) - last(ys) - cin, 1);
      (zs + [diff_out], cout)
  }

  /* Proves seq_sub yields the same value as converting the sequences to nats,
  then subtracting them. */
  lemma lemma_seq_sub_nat(xs: seq<uint>,
                          ys: seq<uint>,
                          zs: seq<uint>,
                          cout: nat)
    requires |xs| == |ys|
    requires seq_sub(xs, ys) == (zs, cout)
    ensures to_nat(xs) - to_nat(ys) + cout * power(BASE(), |xs|) == to_nat(zs)
  {
    reveal seq_sub();
    if |xs| == 0 {
      reveal to_nat();
    } else {
      var pow := power(BASE(), |xs| - 1);
      var (zs', cin) := seq_sub(drop_last(xs), drop_last(ys));
      var z := if last(xs) >= last(ys) + cin
               then last(xs) - last(ys) - cin
               else BASE() + last(xs) - last(ys) - cin;
      assert cout * BASE() + last(xs) - cin - last(ys) == z;

      reveal to_nat_rev();
      lemma_to_nat_eq_to_nat_rev_auto();
      calc {
        to_nat(zs);
        to_nat_rev(zs);
        to_nat_rev(zs') + z * pow;
          { lemma_seq_sub_nat(drop_last(xs), drop_last(ys), zs', cin); }
        to_nat_rev(drop_last(xs)) - to_nat_rev(drop_last(ys)) + cin * pow + z * pow;
          {
            lemma_mul_equality_auto();
            assert pow * (cout * BASE() + last(xs) - cin - last(ys)) == pow * z;
            lemma_mul_is_distributive_auto();
          }
        to_nat_rev(xs) - to_nat_rev(ys) + cout * BASE() * pow;
          {
            lemma_mul_is_associative(cout, BASE(), pow);
            reveal power();
          }
        to_nat_rev(xs) - to_nat_rev(ys) + cout * power(BASE(), |xs|);
        to_nat(xs) - to_nat(ys) + cout * power(BASE(), |xs|);
      }
    }
  }

}

abstract module NatSeq1 refines NatSeq {

  function method BASE1(): nat
		ensures BASE1() > 1

  function method BASE(): nat { BASE1() }

}

abstract module NatSeq2 refines NatSeq {

  import NatSeq1

  function method BASE2(): nat
		ensures BASE2() > 1
      && exists n :: (NatSeq1.BASE() == power(BASE2(), n) && n > 1)

  function method BASE(): nat { BASE2() }

}
