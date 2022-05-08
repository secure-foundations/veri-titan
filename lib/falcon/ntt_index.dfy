include "bins.dfy"
include "pows_of_2.dfy"

module ntt_index {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul

    import opened pows_of_2
    import opened bins

    function method bit_rev_int(i: nat, bound: pow2_t): (ri: nat)
        requires i < bound.full;
        ensures ri < bound.full;
    {
        if bound.exp == 0 then
            i
        else
            reveal Pow2();
            var rs := Reverse(FromNatWithLen(i, bound.exp));
            LemmaSeqNatBound(rs);
            ToNatRight(rs)
    }

    lemma bit_rev_int_basics_lemma(len: pow2_t)
        requires len.full >= 4;
        ensures bit_rev_int(0, len) == 0;
        ensures bit_rev_int(1, len) != 1;
    {
        assume len.exp >= 2;
        reveal Pow2();
        var zero := FromNatWithLen(0, len.exp);
        LemmaSeqZero(zero);
        var zrs := Reverse(zero);
        assert zrs == SeqZero(len.exp);

        var one := FromNatWithLen(1, len.exp);
        var ors := Reverse(one);

        assume ors != one;
        LemmaSeqNeq(ors, one);
    }

    lemma bit_rev_int_lemma0(i: nat, bound: pow2_t)
        requires i < bound.full;
        ensures bit_rev_int(i, pow2_double(bound)) == 2 * bit_rev_int(i, bound);
    {
        var dbound := pow2_double(bound);
        reveal Pow2();

        var bis := FromNatWithLen(i, bound.exp);
        var bdis := FromNatWithLen(i, dbound.exp);
        var normal := FromNat(i);

        assert bdis[bound.exp] == 0 && bdis[..bound.exp] == bis by {
            BitSelModEquivalence(bdis, bound.exp);
            LemmaFundamentalDivModConverse(i, bound.full, 0, i);

            assert ToNatLeft(bdis) == ToNatLeft(bdis[..bound.exp]) by {
                reveal ToNatLeft();
            }

            LemmaToNatLeftEqToNatRight(bdis);
            LemmaToNatLeftEqToNatRight(bdis[..bound.exp]);
            LemmaSeqEq(bdis[..bound.exp], bis);
        }

        calc == {
            bit_rev_int(i, dbound);
            ToNatRight(Reverse(bdis));
            {
                assert Reverse(bdis) == [0] + Reverse(bdis[..bound.exp]);
            }
            ToNatRight([0] + Reverse(bdis[..bound.exp]));
            ToNatRight([0] + Reverse(bis));
            {
                reveal ToNatRight();
            }
            2 * ToNatRight(Reverse(bis));
            2 * bit_rev_int(i, bound);
        }
    }

    lemma bit_rev_int_lemma1(i: nat, bound: pow2_t)
        requires i < bound.full;
        ensures bit_rev_int(i+bound.full, pow2_double(bound)) == 2 * bit_rev_int(i, bound) + 1;
    {
        var j := i+bound.full;
        var dbound := pow2_double(bound);
        reveal Pow2();

        var bis := FromNatWithLen(i, bound.exp);
        var bdis := FromNatWithLen(j, dbound.exp);
        var normal := FromNat(j);

       assert bdis[bound.exp] == 1 && bdis[..bound.exp] == bis by {
            BitSelModEquivalence(bdis, bound.exp);
            LemmaFundamentalDivModConverse(j, bound.full, 1, i);

            assert ToNatLeft(bdis) == ToNatLeft(bdis[..bound.exp]) + bound.full by {
                reveal ToNatLeft();
            }

            LemmaToNatLeftEqToNatRight(bdis);
            LemmaToNatLeftEqToNatRight(bdis[..bound.exp]);
            LemmaSeqEq(bdis[..bound.exp], bis);
        }

        calc == {
            bit_rev_int(j, dbound);
            ToNatRight(Reverse(bdis));
            {
                assert Reverse(bdis) == [1] + Reverse(bdis[..bound.exp]);
            }
            ToNatRight([1] + Reverse(bdis[..bound.exp]));
            ToNatRight([1] + Reverse(bis));
            {
                reveal ToNatRight();
            }
            2 * ToNatRight(Reverse(bis)) + 1;
            2 * bit_rev_int(i, bound) + 1;
        }
    }

    lemma bit_rev_int_lemma2(i: nat, bound: pow2_t)
        requires i < bound.full;
        ensures bit_rev_int(2 * i, pow2_double(bound)) == bit_rev_int(i, bound);
    {
        var dbound := pow2_double(bound);
        reveal Pow2();

        var bis := FromNatWithLen(i, bound.exp);
        var bdis := FromNatWithLen(2 * i, dbound.exp);

        assert bdis[0] == 0 && bdis[1..] == bis by {
            BitSelModEquivalence(bdis, 0);
            LemmaPow0(2);
            LemmaModMultiplesBasic(2 * i, 2);
            assert bdis[0] == 0 % 2;
            LemmaSmallMod(0, 2);
            LemmaFundamentalDivModConverse(2 * i, 2, i, 0);

            assert ToNatRight(bdis) == 2 * ToNatRight(bdis[1..]) by {
                reveal ToNatRight();
            }

            LemmaToNatLeftEqToNatRight(bdis);
            LemmaToNatLeftEqToNatRight(bdis[1..]);
            LemmaSeqEq(bdis[1..], bis);
        }

        calc == {
            bit_rev_int(2 * i, dbound);
            ToNatRight(Reverse(bdis));
            {
                assert Reverse(bdis) == Reverse(bdis[1..]) + [0];
            }
            ToNatRight(Reverse(bdis[1..]) + [0]);
            ToNatRight(Reverse(bis) + [0]);
            {
                LemmaToNatLeftEqToNatRight(Reverse(bis) + [0]);
            }
            ToNatLeft(Reverse(bis) + [0]);
            {
                reveal ToNatLeft();
            }
            ToNatLeft(Reverse(bis)) + 0 * Pow(2, bound.exp);
            {
                LemmaMulByZeroIsZeroAuto();
            }
            ToNatLeft(Reverse(bis));
            {
                LemmaToNatLeftEqToNatRight(Reverse(bis));

            }
            bit_rev_int(i, bound);
        }
    }

    lemma bit_rev_int_lemma3(i: nat, bound: pow2_t)
        requires i < bound.full;
        ensures bit_rev_int(2 * i + 1, pow2_double(bound)) ==  bit_rev_int(i, bound) + bound.full;
    {
        var dbound := pow2_double(bound);
        var j := 2 * i + 1;

        reveal Pow2();

        var bis := FromNatWithLen(i, bound.exp);
        var bdis := FromNatWithLen(j, dbound.exp);

        assert bdis[0] == 1 && bdis[1..] == bis by {
            BitSelModEquivalence(bdis, 0);
            LemmaPow0(2);
            LemmaModMultiplesBasic(2 * i, 2);
            assert bdis[0] == 1 % 2;
            LemmaSmallMod(1, 2);
            LemmaFundamentalDivModConverse(j, 2, i, 1);

            assert ToNatRight(bdis) == 2 * ToNatRight(bdis[1..]) + 1 by {
                reveal ToNatRight();
            }

            LemmaToNatLeftEqToNatRight(bdis);
            LemmaToNatLeftEqToNatRight(bdis[1..]);
            LemmaSeqEq(bdis[1..], bis);
        }

        calc == {
            bit_rev_int(j, pow2_double(bound));
            ToNatRight(Reverse(bdis));
            {
                assert Reverse(bdis) == Reverse(bdis[1..]) + [1];
            }
            ToNatRight(Reverse(bdis[1..]) + [1]);
            ToNatRight(Reverse(bis) + [1]);
            {
                LemmaToNatLeftEqToNatRight(Reverse(bis) + [1]);
            }
            ToNatLeft(Reverse(bis) + [1]);
            {
                reveal ToNatLeft();
            }
            ToNatLeft(Reverse(bis)) + 1 * Pow(2, bound.exp);
            ToNatLeft(Reverse(bis)) + bound.full;
            {
                LemmaToNatLeftEqToNatRight(Reverse(bis));
            }
            bit_rev_int(i, bound) + bound.full;
        }
    }
    
    predicate {:opaque} is_bit_rev_shuffle<T>(a: seq<T>, b: seq<T>, len: pow2_t)
        requires |a| == |b| == len.full;
    {
        forall i | 0 <= i < len.full ::
            a[i] ==  b[bit_rev_int(i, len)]
    }

    lemma bit_rev_symmetric(i: nat, bound: pow2_t)
        requires i < bound.full;
        ensures bit_rev_int(bit_rev_int(i, bound), bound) == i;
    {
        if bound.exp != 0 {
            reveal Pow2();
            var s := FromNatWithLen(i, bound.exp);
            var rs := Reverse(s);
            var rrs := Reverse(rs); 
            var rbi := bit_rev_int(i, bound);
            assert rbi == ToNatRight(rs);

            assert FromNatWithLen(rbi, bound.exp) == rs by {
                LemmaSeqEq(rs, FromNatWithLen(rbi, bound.exp));
            }

            calc == {
                bit_rev_int(rbi, bound);
                ToNatRight(Reverse(rs));
                ToNatRight(Reverse(rs));
                ToNatRight(rrs);
                {
                    ReverseSymmetric(s);
                    assert rrs == s;
                }
                ToNatRight(s);
            }
        }
    }

    lemma bit_rev_shuffle_symmetric<T>(a: seq<T>, b: seq<T>, len: pow2_t)
        requires |a| == |b| == len.full;
        requires is_bit_rev_shuffle(a, b, len);
        ensures is_bit_rev_shuffle(b, a, len);
    {
        reveal is_bit_rev_shuffle();
        forall i | 0 <= i < len.full
            ensures b[i] == a[bit_rev_int(i, len)]
        {
            var j := bit_rev_int(i, len);
            calc == {
                b[i];
                {
                    bit_rev_symmetric(i, len);
                }
                b[bit_rev_int(j, len)];
                a[j];
            }
        }
    }

    predicate {:opaque} is_set_min(x: nat, s: set<nat>)
    {
        forall t | t in s :: x <= t
    }

    function {:opaque} minimum(s: set<nat>): (x: nat)
        requires |s| >= 1;
        ensures is_set_min(x, s);
        ensures x in s;
    {
        reveal is_set_min();
        var y :| y in s;
        var s' := s - {y};

        if |s| == 1 then
            assert y in s;
            assert |s'| == 0;
            assert s' == {};
            assert s == {y};
            y
        else 
            var m := minimum(s');
            var x := (if y < m then y else m);
            assert is_set_min(x, s) by {
                forall t | t in s
                    ensures x <= t
                {
                    if t in s' {
                        assert x <= m <= t;
                    } else {
                        assert x <= y;
                    }
                }
            }
            x
    }

    // lemma set_min_uiique(s: set<nat>): (x: nat)
    // {
    datatype rev_view = rev_view(
        finished: set<nat>,
        unfinished: set<nat>,
        len: pow2_t)
    {
        predicate {:opaque} rev_view_wf()
        {
            && (forall bi | (bi in finished || bi in unfinished) ::
                0 <= bi < len.full)
            && (finished !! unfinished)
            && (finished + unfinished == set bi | 0 <= bi < len.full :: bi)
            && len.full >= 4
        }

        lemma buff_index_state_lemma(bi: nat)
            requires bi < len.full;
            requires rev_view_wf();
            ensures (bi in finished) != (bi in unfinished)
        {
            reveal rev_view_wf();
            if bi in finished {
                assert bi !in unfinished;
            }
            if bi in unfinished {
                assert bi !in finished;
            }
        }
  
        lemma rev_entry_wf_lemma(bi: nat)
            requires rev_view_wf();
            requires bi in finished || bi in unfinished;
            ensures bi < len.full
        {
            reveal rev_view_wf();
        }
    
        predicate index_is_shuffled<T>(a: seq<T>, b: seq<T>, bi: nat)
            requires bi < len.full;
            requires |a| == |b| == len.full;
            requires rev_view_wf();
        {
            var rbi := bit_rev_int(bi, len);
            && a[bi] == b[rbi]
            && a[rbi] == b[bi]
        }

        function get_split_index(): (bi: nat)
            requires |unfinished| != 0;
            requires rev_view_wf();
            ensures bi < len.full;
            ensures bi !in finished;
        {
            var bi := minimum(unfinished);
            rev_entry_wf_lemma(bi);
            buff_index_state_lemma(bi);
            bi
        }

        predicate {:opaque} partially_shuffled_inv<T>(a: seq<T>, b: seq<T>)
            requires |a| == |b| == len.full;
            ensures partially_shuffled_inv(a, b) ==> rev_view_wf();
        {
            && rev_view_wf()
            && reveal rev_view_wf();
            && |unfinished| != 0
            && var split_index := get_split_index();
            && (forall bi | bi in finished :: bit_rev_int(bi, len) in finished)
            && (forall bi | bi in unfinished :: bit_rev_int(bi, len) in unfinished)
            && (forall bi | bi in finished :: index_is_shuffled(a, b, bi))
            && (forall bi | 0 <= bi < split_index :: bi in finished)
        }

        static function init_finished(len: pow2_t): set<nat>
            requires len.full >= 4;
        {
            set bi: nat | (0 <= bi < len.full && bi == bit_rev_int(bi, len)) :: bi
        }

        static function init_unfinished(len: pow2_t): set<nat>
            requires len.full >= 4;
        {
            set bi: nat | (0 <= bi < len.full && bi != bit_rev_int(bi, len)) :: bi
        }

        static function {:opaque} init_rev_view<T>(a: seq<T>, len: pow2_t): (r: rev_view)
            requires |a| == len.full >= 4;
            ensures r.len == len;
            // ensures r.partially_shuffled_inv(a, a);
        {    
            var finished := rev_view.init_finished(len);
            var unfinished := rev_view.init_unfinished(len);
            rev_view(finished, unfinished, len)
        }

        static lemma init_unfinished_lemma(len: pow2_t)
            requires len.full >= 4;
            ensures 1 in init_unfinished(len);
            ensures |init_unfinished(len)| != 0;
            ensures minimum(init_unfinished(len)) == 1;
        {
            var unfinished := init_unfinished(len);
            bit_rev_int_basics_lemma(len);
            assert 1 in unfinished;
            assert |unfinished| != 0;
            assert |unfinished| >= 1;
            assume minimum(init_unfinished(len)) == 1;
        }

        lemma init_rev_view_inv_lemma<T>(a: seq<T>, len: pow2_t)
            requires |a| == len.full >= 4;
            requires this == init_rev_view(a, len);
        {
            reveal init_rev_view();

            assert finished !! unfinished;
            assert finished + unfinished == set bi | 0 <= bi < len.full :: bi;

            bit_rev_int_basics_lemma(len);

            forall bi | bi in finished
                ensures bit_rev_int(bi, len) in finished
            {}

            forall bi | bi in unfinished 
                ensures bit_rev_int(bi, len) in unfinished;
            {
                var bri := bit_rev_int(bi, len);
                if  bri !in unfinished {
                    assert bri in finished;
                    assert bit_rev_int(bri, len) in finished;
                    bit_rev_symmetric(bi, len);
                    assert bi in finished;
                    assert false;
                }
            }

            forall bi | bi in finished
                ensures index_is_shuffled(a, a, bi)
            {}

            assert rev_view_wf() by {
                reveal rev_view_wf();
            }


            init_unfinished_lemma(len);
            var split_index := get_split_index();
            assume split_index == 1;
  
            forall bi | 0 <= bi < split_index
                ensures bi in finished
            {
                assert bi == 0;
                assert bit_rev_int(0, len) == 0;
            }
        }

        // function next_rev_view<T>(a: seq<T>, b: seq<T>): (r: rev_view)
        //     requires |unfinished| != 0;
        //     requires |a| == |b| == len.full;
        //     requires partially_shuffled_inv(a, b);
        // {
        //     var bi :=  get_split_index();
        //     rev_view(finished + {bi, bit_rev_int(bi, len)},
        //         unfinished - {bi, bit_rev_int(bi, len)},
        //         len)
        // }

        // lemma next_rev_view_lemma<T>(a: seq<T>, b: seq<T>, bj: nat, r: rev_view)
        //     requires bj < |a| == |b| == len.full;
        //     requires partially_shuffled_inv(a, b, bj);
        //     requires bj !in finished;
        //     requires r == next_rev_view(a, b, bj);
        // {
        //     // var rbj := bit_rev_int(bj, len);
        //     // var c := b[bj := c[rbj]][rbj := c[bj]];

        //     // assert r.partially_shuffled_inv(a, c, bj);

        // }
    }

    datatype rev_table = rev_table(
        table: seq<(nat, nat)>,
        len: pow2_t)
    {
        predicate table_entry_wf(ti: nat)
            requires ti < |table|;
        {
            && ti <= table[ti].0
            && table[ti].0 < len.full
            && table[ti].1 < len.full
            && table[ti].0 == bit_rev_int(table[ti].1, len)
            && table[ti].1 == bit_rev_int(table[ti].0, len)
        }

        predicate {:opaque} rev_table_wf()
            ensures rev_table_wf() ==> len.full >= 4
            ensures rev_table_wf() ==> |table| >= 2
        {
            && (forall ti | 0 <= ti < |table| :: table_entry_wf(ti))
            // table is sorted in terms of the key (src) index
            && (forall ti, tj | 0 <= ti < tj < |table| :: table[ti].0 < table[tj].0)
            && len.full >= 4
            && |table| >= 2
        }

        lemma table_entry_wf_lemma(ti: nat)
            requires 0 <= ti < |table|
            requires rev_table_wf();
            ensures table_entry_wf(ti);
        {
            reveal rev_table_wf();
        }

        // bi is a buffer index (NOT a table index)
        predicate in_table(bi: nat)
            requires bi < len.full;
        {
            exists ti: nat :: (
                ti < |table| && table[ti].0 == bi)
        }

        // given a (bi) buffer index, return the (ti) table index 
        function get_table_index(bi: nat): (ti: nat)
            requires rev_table_wf();
            requires bi < len.full;
            requires in_table(bi);
            ensures ti < |table|;
            ensures table_entry_wf(ti);
        {
            var ti: nat :| (ti < |table| && table[ti].0 == bi);
            table_entry_wf_lemma(ti);
            ti
        }

        function get_buffer_index(ti: nat): (bi: nat)
            requires rev_table_wf();
            requires ti < |table|;
            ensures table_entry_wf(ti);
        {
            table_entry_wf_lemma(ti);
            table[ti].0
        }

        function buffer_prefix_index(ti: nat): nat 
            requires rev_table_wf();
            requires ti <= |table|;
        {
            if ti == |table| then len.full else get_buffer_index(ti)
        }

        predicate prefix_prev_bi_properties(ti: nat, bi: nat)
            requires rev_table_wf();
            requires ti < |table|;
            requires bi < buffer_prefix_index(ti);
        {
            var split_index := buffer_prefix_index(ti);
            var rbi := bit_rev_int(bi, len);
            && (!in_table(bi) ==> (
                || (bi == rbi)
                || (in_table(rbi) && 0 <= rbi < split_index)))
            && (in_table(bi) ==> 
                && (bi != rbi)
                && (!in_table(rbi)))
        }

        predicate bit_rev_table_prefix_inv(ti: nat)
            requires ti < |table|;
            requires rev_table_wf();
        {
            var split_index := buffer_prefix_index(ti);
            forall bi | (0 <= bi < split_index) ::
                prefix_prev_bi_properties(ti, bi)
        }

        predicate {:opaque} bit_rev_table_inv()
            ensures bit_rev_table_inv() ==> rev_table_wf()
        {
            && rev_table_wf()
            && (forall ti | 0 <= ti < |table| :: 
                bit_rev_table_prefix_inv(ti))
        }

        // lemma partially_shuffled_inv_peri_lemma<T>(
        //     a: seq<T>, b: seq<T>, c: seq<T>,
        //     ti: nat, i: nat, j: nat,
        //     view: rev_view)
        //     requires |a| == |b| == |c| == len.full;
        //     requires ti < |table|;
        //     requires bit_rev_table_inv();
        //     requires buffer_prefix_index(ti) < len.full;
        //     requires view.len == len;
        //     requires i == table[ti].0 < len.full;
        //     requires j == table[ti].1 < len.full;
        //     requires view.partially_shuffled_inv(a, b, buffer_prefix_index(ti));
        //     requires c == b[i := b[j]][j := b[i]];
        // {

        // }


        // method bit_rev<T>(a: seq<T>) returns (b: seq<T>)
        //     requires |a| == len.full;
        //     requires bit_rev_table_inv();
        // {
        //     b := a;
        //     var ti := 0;

        //     ghost var view := rev_view.init_rev_view(a, len);

        //     assume buffer_prefix_index(0) == 1;

        //     while ti < |table|
        //         invariant |b| == len.full;
        //         invariant view.
        //             partially_shuffled_inv(a, b, buffer_prefix_index(ti));
        //         decreases |table| - ti;
        //     {
        //         var prev_b := b;

        //         var i := table[ti].0;
        //         var j := table[ti].1;

        //         table_entry_wf_lemma(ti);

        //         var temp := b[i];
        //         b := b[i := b[j]];
        //         b := b[j := temp];

        //         partially_shuffled_inv_peri_lemma(a, prev_b, b, ti, i, j, view);
        //         ti := ti + 1;
        //         assume false;
        //     }
        // }
    }
}

        // lemma buffer_prefix_index_lemma<T>(a: seq<T>, bi: nat)
        //     requires bit_rev_table_inv();
        //     requires finished == inital_finished_set();
        //     requires bi < len.full;
        //     requires |a| == len.full;
        // {
        //     var split_index := buffer_prefix_index(0);
        //     var ti := 0;

        //     // reveal inital_finished_set();

        //     reveal partially_shuffled_inv();
        //     assert bit_rev_table_prefix_inv(ti) by {
        //         reveal bit_rev_table_inv();
        //     }
  
        //     if 0 <= bi < len.full && finished_set_membership(a, a, bi, ti) {
        //         // assert prev_bi_properties(ti, bi);

        //     //   var rbi := bit_rev_int(bi, len);
        //     //     assert  && (!in_table(bi) ==> (
        //     //         || (bi == rbi)
        //     //         || (in_table(rbi) && 0 <= rbi < split_index)))
        //     //     && (in_table(bi) ==> 
        //     //         && (bi != rbi)
        //     //         && (!in_table(rbi)));

        //     }
        // }

        // lemma inital_finished_set_lemma<T>(a: seq<T>)
        //     requires bit_rev_table_inv();
        //     requires |a| == len.full;
        //     requires finished == inital_finished_set();
        //     // ensures partially_shuffled_inv(a, a, 0);
        // {
        //     reveal inital_finished_set();
        //     reveal partially_shuffled_inv();

        //     var ti := 0;
        //     assume bit_rev_int(0, len) == 0;

        //     forall bi | 0 <= bi < len.full && bi in finished
        //         ensures finished_set_membership(a, a, bi, ti);
        //     {
        //         var rbi := bit_rev_int(bi, len);
        //         var split_index := 0;
        //         assert rbi == bi;
        //     }
        
        //     assert bit_rev_table_prefix_inv(ti) by {
        //         reveal bit_rev_table_inv();
        //     }

        //     forall bi | 0 <= bi < len.full && finished_set_membership(a, a, bi, ti)
        //         ensures bi in finished;
        //     {
        //         var rbi := bit_rev_int(bi, len);
        //         var split_index := buffer_prefix_index(ti);
        //         assert a[bi] == a[rbi];
        //         assert a[rbi] == a[bi];

        //         if 0 <= bi < split_index {
        //             assume false;
        //         } else {
        //             assert bi == bit_rev_int(bi, len); 
        //         }

        //         // assert bi == bit_rev_int(bi, len)            
        //     }

        // }

        // lemma partially_shuffled_inv_lemma<T>(
        //     a: seq<T>, b: seq<T>, c: seq<T>,
        //     finished: set<nat>, 
        //     ti: nat, i: nat, j: nat)
        //     requires bit_rev_table_inv();
        //     requires |a| == |b| == |c| == len.full;
        //     requires ti < |table|;
        //     requires i < len.full;
        //     requires i == table[ti].0;
        //     requires j < len.full;
        //     requires j == table[ti].1;
        //     requires partially_shuffled_inv(a, b, finished);
        //     requires c == b[i := b[j]][j := b[i]];
        // {
        //     var new_finished := finished + {i, j};
        //     reveal partially_shuffled_inv();
        //     table_entry_wf_lemma(ti);

        //     forall bi | bi in new_finished
        //         ensures 0 <= bi < len.full
        //     {
        //         if bi != i && bi != j {
        //             assert bi in finished;
        //         }
        //     }
            
        //     forall bi | 0 <= bi < len.full && bi in new_finished
        //         ensures c[bi] == a[bit_rev_int(bi, len)]
        //         // ensures c[bit_rev_int(bi, len)] == a[bi]
        //     {
        //         if bi == i {
        //             assert c[i] == b[j];
        //             assert j !in finished;
        //             assume false;
        //         } else if bi == j {
        //             assume false;
        //         } else {
        //             assert c[bi] == b[bi];
        //         }
        //     }
        //     // && (forall bi | 0 <= bi < len.full && bi !in finished :: (
        //     //     && b[bi] == a[bi]))
        // }

