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

    lemma bit_rev_unique(i: nat, j: nat, bound: pow2_t)
        requires i < bound.full;
        requires j < bound.full;
        requires i != j;
        ensures bit_rev_int(i, bound) != bit_rev_int(j, bound);
    {
        reveal Pow2();
        var si := FromNatWithLen(i, bound.exp);
        var sj := FromNatWithLen(j, bound.exp);

        if si == sj {
            LemmaSeqEq(si, sj);
            assert false;
        }
        
        var rsi := Reverse(si);
        var rsj := Reverse(sj);

        if rsi == rsj {
            assume si == sj;
        }

        LemmaSeqNeq(rsi, rsj);
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
            a[i] == b[bit_rev_int(i, len)]
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
        && x in s
        && (forall t | t in s :: x <= t)
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

    lemma set_min_unique_lemma(s: set<nat>, x: nat)
        requires |s| >= 1;
        requires is_set_min(x, s);
        ensures minimum(s) == x;
    {
        var y := minimum(s);

        assert y <= x by {
            assert is_set_min(y, s);
            reveal is_set_min();
            assert x in s;
        }

        assert x <= y by {
            assert is_set_min(x, s);
            reveal is_set_min();
            assert y in s;
        }
    }

    datatype rev_view<T> = rev_view(
        // a: seq<T>,
        b: seq<T>,
        finished: set<nat>,
        unfinished: set<nat>,
        len: pow2_t)

        // table: seq<(nat, nat)>,
        // ti: nat)
    {
        predicate {:opaque} rev_view_wf()
            ensures rev_view_wf() ==> len.full >= 4
            ensures rev_view_wf() ==> |b| == len.full;
        {
            && (forall bi | (bi in finished || bi in unfinished) ::
                0 <= bi < len.full)
            && (finished !! unfinished)
            && (finished + unfinished == set bi | 0 <= bi < len.full :: bi)
            && len.full >= 4
            && |b| == len.full
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
    
        predicate index_is_shuffled(a: seq<T>, bi: nat)
            requires |a| == len.full;
            requires bi < len.full;
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

        function get_split_index_wrap(): nat
            requires rev_view_wf();
        {
            if |unfinished| != 0 then get_split_index() else len.full
        }

        predicate {:opaque} finished_shuffle_inv(a: seq<T>)
            requires |a| == len.full;
            requires rev_view_wf()
        {
            && reveal rev_view_wf();
            && (forall bi | bi in finished ::(
                && bit_rev_int(bi, len) in finished
                && index_is_shuffled(a, bi)))
        }

        predicate {:opaque} unfinished_shuffle_inv(a: seq<T>)
            requires |a| == len.full;
            requires rev_view_wf()
        {
            && reveal rev_view_wf();
            && (forall bi | bi in unfinished :: (
                && bit_rev_int(bi, len) in unfinished
                && a[bi] == b[bi]))
        }

        predicate {:opaque} shuffle_prefix_inv()
            requires rev_view_wf();
        {
            var split_index := get_split_index_wrap();
            && (forall bi | 0 <= bi < split_index :: bi in finished)
        }

        // // predicate {:opaque} table_prefix_inv()
        // // {
        // //     && ti == |table| - 1
        // //     && table[ti] == 
        // // }

        predicate shuffle_inv(a: seq<T>)
            requires |a| == len.full;
            ensures shuffle_inv(a) ==> rev_view_wf();
        {
            && rev_view_wf()
            && finished_shuffle_inv(a)
            && unfinished_shuffle_inv(a)
            && shuffle_prefix_inv()
        }

        lemma split_index_unfinished_lemma(a: seq<T>)
            requires |a| == len.full;
            requires shuffle_inv(a);
            requires |unfinished| != 0;
            ensures get_split_index() in unfinished;
            ensures get_split_index() !in finished;
            ensures bit_rev_int(get_split_index(), len) in unfinished;
            ensures bit_rev_int(get_split_index(), len) !in finished;
        {
            var bi := get_split_index();
            var rbi := bit_rev_int(bi, len);
            reveal unfinished_shuffle_inv();
            assert rbi in unfinished;
            buff_index_state_lemma(rbi);
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

        static function {:opaque} init_rev_view(a: seq<T>, len: pow2_t): (r: rev_view<T>)
            requires |a| == len.full >= 4;
            ensures r.len == len;
            ensures r.rev_view_wf();
        {    
            var finished := rev_view<T>.init_finished(len);
            var unfinished := rev_view<T>.init_unfinished(len);
            var r := rev_view(a, finished, unfinished, len);
            reveal r.rev_view_wf();
            assert r.rev_view_wf();
            r
        }

        lemma init_unfinished_lemma(a: seq<T>, len: pow2_t)
            requires |a| == len.full >= 4;
            requires this == init_rev_view(a, len);
            ensures 0 in finished;
            ensures 1 in unfinished;
            ensures |unfinished| != 0;
            ensures get_split_index() == 1;
        {
            reveal init_rev_view();
            bit_rev_int_basics_lemma(len);
            assert 1 in unfinished;
            assert |unfinished| != 0;
            assert |unfinished| >= 1;
            assert is_set_min(1, unfinished) by {
                reveal is_set_min();
            }
            set_min_unique_lemma(unfinished, 1);
            assert minimum(unfinished) == 1;
        }

        lemma shuffle_inv_pre_lemma(a: seq<T>, len: pow2_t)
            requires |a| == len.full >= 4;
            requires this == init_rev_view(a, len);
            ensures this.shuffle_inv( a);
        {
            bit_rev_int_basics_lemma(len);

            assert finished_shuffle_inv(a) by {
                reveal finished_shuffle_inv();
                forall bi | bi in finished
                    ensures bit_rev_int(bi, len) in finished;
                    ensures index_is_shuffled(a, bi);
                {
                    reveal init_rev_view();
                }
            }

            assert unfinished_shuffle_inv(a) by {
                reveal unfinished_shuffle_inv();
                forall bi | bi in unfinished
                    ensures bit_rev_int(bi, len) in unfinished;
                    ensures a[bi] == a[bi];
                {
                    reveal init_rev_view();
                    var bri := bit_rev_int(bi, len);
                    if  bri !in unfinished {
                        assert bri in finished;
                        assert bit_rev_int(bri, len) in finished;
                        bit_rev_symmetric(bi, len);
                        assert bi in finished;
                        assert false;
                    }
                }
            }

            init_unfinished_lemma(a, len);

            assert shuffle_prefix_inv() by {
                reveal shuffle_prefix_inv();
                var split_index := get_split_index();
    
                forall bi | 0 <= bi < split_index
                    ensures bi in finished
                {
                    assert bi == 0;
                    assert bit_rev_int(0, len) == 0;
                }
            }
        }

        function next_rev_buffer(): (c: seq<T>)
            requires |b| == len.full;
            requires rev_view_wf();
        {
            if |unfinished| != 0 then 
                var sbj := get_split_index();
                var rsbj := bit_rev_int(sbj, len);
                b[sbj := b[rsbj]][rsbj := b[sbj]]
            else
                b
        }

        function next_rev_view(a: seq<T>): (r: rev_view<T>)
            requires |a| == len.full;
            requires shuffle_inv(a);
            ensures r.rev_view_wf();
        {
            if |unfinished| != 0 then 
                var bi := get_split_index();
                var rbi := bit_rev_int(bi, len);
                var r := rev_view(
                    next_rev_buffer(),
                    finished + {bi, rbi},
                    unfinished - {bi, rbi},
                    len);
                reveal r.rev_view_wf();
                assert r.rev_view_wf();
                r
            else
                this
        }

        lemma shuffle_inv_peri_lemma(a: seq<T>, next: rev_view<T>)
            requires |a| == len.full;
            requires shuffle_inv(a);
            requires |unfinished| != 0;
            requires next == next_rev_view(a);
            ensures next.shuffle_inv(a);
        {
            var sbj := get_split_index();
            var rsbj := bit_rev_int(sbj, len);
            var c := b[sbj := b[rsbj]][rsbj := b[sbj]];

            split_index_unfinished_lemma(a);

            assert next.finished_shuffle_inv(a) by {
                forall bi | bi in next.finished
                    ensures bit_rev_int(bi, len) in next.finished;
                {
                    next.rev_entry_wf_lemma(bi);
                    if bi in finished {
                        reveal finished_shuffle_inv();
                        assert bit_rev_int(bi, len) in finished;
                        assert bit_rev_int(bi, len) in next.finished;
                    } else if bi == sbj {
                        assert bit_rev_int(bi, len) in next.finished;
                    } else {
                        assert bi == bit_rev_int(sbj, len);
                        bit_rev_symmetric(sbj, len);
                        assert bit_rev_int(bit_rev_int(sbj, len), len) == sbj;
                        assert sbj in next.finished;
                    }
                }

                forall bi | bi in next.finished
                    ensures next.index_is_shuffled(a, bi)
                {
                    next.rev_entry_wf_lemma(bi);
                    var rbi := bit_rev_int(bi, len);
                    if bi in finished {
                        reveal finished_shuffle_inv();
                        bit_rev_unique(bi, sbj, len);
                        bit_rev_symmetric(sbj, len);
                        bit_rev_unique(bi, rsbj, len);
                        assert index_is_shuffled(a, bi);
                        assert b[bi] == c[bi];
                        assert b[rbi] == c[rbi];
                    } else if bi == sbj {
                        assert a[bi] == b[bi] && a[rbi] == b[rbi] by {
                            assert sbj in unfinished;
                            assert rsbj in unfinished;
                            reveal unfinished_shuffle_inv();
                        }
                        assert next.index_is_shuffled(a, sbj) by {
                            assert a[sbj] == c[rsbj];
                            assert a[rsbj] == c[sbj];
                        }
                    } else {
                        assert bi == rsbj;
                        assert a[bi] == b[bi] && a[rbi] == b[rbi] by {
                            assert sbj in unfinished;
                            assert rsbj in unfinished;
                            reveal unfinished_shuffle_inv();
                        }
                        bit_rev_symmetric(sbj, len);
                        assert next.index_is_shuffled(a, bi) by {
                            assert a[sbj] == c[rsbj];
                            assert a[rsbj] == c[sbj];
                        }
                    }
                }
                reveal next.finished_shuffle_inv();
            }

            assert next.unfinished_shuffle_inv(a) by {
                forall bi | bi in next.unfinished
                    ensures bit_rev_int(bi, len) in next.unfinished
                {
                    next.rev_entry_wf_lemma(bi);
                    assert bi != sbj && bi != rsbj;

                    var rbi := bit_rev_int(bi, len);
                    reveal unfinished_shuffle_inv();
                    assert bi in unfinished;
                    assert rbi in unfinished;

                    assert rbi != rsbj by {
                        bit_rev_unique(bi, sbj, len);
                    }

                    assert rbi != sbj by {
                        bit_rev_symmetric(sbj, len);
                        bit_rev_unique(bi, rsbj, len);
                    }
                }

                forall bi | bi in next.unfinished
                    ensures a[bi] == c[bi];
                {
                    next.rev_entry_wf_lemma(bi);
                    assert bi in unfinished;
                    reveal unfinished_shuffle_inv();
                    assert a[bi] == b[bi] == c[bi];
                }
                reveal next.unfinished_shuffle_inv();
            }

            assert next.shuffle_prefix_inv() by {
                var nsbj := next.get_split_index_wrap();
                forall bi | 0 <= bi < nsbj
                    ensures bi in next.finished
                {
                    if bi < sbj {
                        reveal shuffle_prefix_inv();
                        assert bi in finished;
                    } else if bi == sbj || bi == rsbj {
                        assert bi in next.finished;
                    } else {
                        assert bi < nsbj;
                        if bi !in finished {
                            buff_index_state_lemma(bi);
                            assert bi in unfinished;
                            assert bi in next.unfinished;
                            assert is_set_min(nsbj, next.unfinished);
                            reveal is_set_min();
                            assert false;
                        }
                    }
                }

                reveal next.shuffle_prefix_inv();
            }
        }

        lemma shuffle_inv_post_lemma(a: seq<T>)
            requires |a| == len.full;
            requires shuffle_inv(a);
            // requires get_split_index_wrap() == len.full;
            requires |unfinished| == 0;
            ensures is_bit_rev_shuffle(a, b, len);
        {
            assert finished == set bi: nat | (0 <= bi < len.full) :: bi by {
                reveal rev_view_wf();
            }

            assert is_bit_rev_shuffle(a, b, len) by {
                reveal is_bit_rev_shuffle();
                reveal finished_shuffle_inv();
            }
        }
    }

    // function build_view(a: seq<T>, i: nat, len: pow2_t): rev_view
    //     requires len.full >= 4;
    // {
    //     if i == 0 then 
    //         init_rev_view(len)
    //     else
    //         build_view(i - 1).next_rev_view()
    // }


    // predicate table_wf(, len: pow2_t)
    // {
    //     forall i in |table| :: 


    // }

    // method bit_rev<T>(a: seq<T>, len: pow2_t, table: seq<(nat, nat)>)
    //     returns (b: seq<T>)

    //     requires |a| == len.full >= 4;
    // {
    //     b := a;
    //     var ti := 0;

    //     ghost var view := rev_view.init_rev_view(len);
    //     view.shuffle_inv_pre_lemma(a, len);

    //     while ti < |table|
    //         invariant |a| == |b| == view.len.full;
    //         invariant view.shuffle_inv(a);
    //     {
    //         // var sbj := get_split_index();
    //         var prev_b := b;

    //         var i := table[ti].0;
    //         var j := table[ti].1;

    //         assume i == view.get_split_index();
    //         assume j == bit_rev_int(i, view.len);

    //         var temp := b[i];
    //         b := b[i := b[j]];
    //         b := b[j := temp];

    //         var next_view := view.next_rev_view(a, prev_b);
    //         view.shuffle_inv_peri_lemma(a, prev_b, next_view);
    //         assert b == view.next_rev_buffer(a, prev_b);
    
    //         view := next_view;
    //     }
    //     //     invariant view.
    //     //         shuffle_inv(a, b, buffer_prefix_index(ti));
    //     //     decreases |table| - ti;
    //     // {

    //     //     // shuffle_inv_peri_lemma(a, prev_b, b, ti, i, j, view);
    //     //     // ti := ti + 1;
    //     //     assume false;
    //     // }
    // }

    // datatype rev_table = rev_table(
    //     table: seq<(nat, nat)>,
    //     len: pow2_t)
    // {
    //     predicate table_entry_wf(ti: nat)
    //         requires ti < |table|;
    //     {
    //         && ti <= table[ti].0
    //         && table[ti].0 < len.full
    //         && table[ti].1 < len.full
    //         && table[ti].0 == bit_rev_int(table[ti].1, len)
    //         && table[ti].1 == bit_rev_int(table[ti].0, len)
    //     }

    //     predicate {:opaque} rev_table_wf()
    //         ensures rev_table_wf() ==> len.full >= 4
    //         ensures rev_table_wf() ==> |table| >= 2
    //     {
    //         && (forall ti | 0 <= ti < |table| :: table_entry_wf(ti))
    //         // table is sorted in terms of the key (src) index
    //         && (forall ti, tj | 0 <= ti < tj < |table| :: table[ti].0 < table[tj].0)
    //         && len.full >= 4
    //         && |table| >= 2
    //     }

    //     lemma table_entry_wf_lemma(ti: nat)
    //         requires 0 <= ti < |table|
    //         requires rev_table_wf();
    //         ensures table_entry_wf(ti);
    //     {
    //         reveal rev_table_wf();
    //     }

    //     // bi is a buffer index (NOT a table index)
    //     predicate in_table(bi: nat)
    //         requires bi < len.full;
    //     {
    //         exists ti: nat :: (
    //             ti < |table| && table[ti].0 == bi)
    //     }

    //     // given a (bi) buffer index, return the (ti) table index 
    //     function get_table_index(bi: nat): (ti: nat)
    //         requires rev_table_wf();
    //         requires bi < len.full;
    //         requires in_table(bi);
    //         ensures ti < |table|;
    //         ensures table_entry_wf(ti);
    //     {
    //         var ti: nat :| (ti < |table| && table[ti].0 == bi);
    //         table_entry_wf_lemma(ti);
    //         ti
    //     }

    //     function get_buffer_index(ti: nat): (bi: nat)
    //         requires rev_table_wf();
    //         requires ti < |table|;
    //         ensures table_entry_wf(ti);
    //     {
    //         table_entry_wf_lemma(ti);
    //         table[ti].0
    //     }

    //     function buffer_prefix_index(ti: nat): nat 
    //         requires rev_table_wf();
    //         requires ti <= |table|;
    //     {
    //         if ti == |table| then len.full else get_buffer_index(ti)
    //     }

    //     predicate prefix_prev_bi_properties(ti: nat, bi: nat)
    //         requires rev_table_wf();
    //         requires ti < |table|;
    //         requires bi < buffer_prefix_index(ti);
    //     {
    //         var split_index := buffer_prefix_index(ti);
    //         var rbi := bit_rev_int(bi, len);
    //         && (!in_table(bi) ==> (
    //             || (bi == rbi)
    //             || (in_table(rbi) && 0 <= rbi < split_index)))
    //         && (in_table(bi) ==> 
    //             && (bi != rbi)
    //             && (!in_table(rbi)))
    //     }

    //     predicate bit_rev_table_prefix_inv(ti: nat)
    //         requires ti < |table|;
    //         requires rev_table_wf();
    //     {
    //         var split_index := buffer_prefix_index(ti);
    //         forall bi | (0 <= bi < split_index) ::
    //             prefix_prev_bi_properties(ti, bi)
    //     }

    //     predicate {:opaque} bit_rev_table_inv()
    //         ensures bit_rev_table_inv() ==> rev_table_wf()
    //     {
    //         && rev_table_wf()
    //         && (forall ti | 0 <= ti < |table| :: 
    //             bit_rev_table_prefix_inv(ti))
    //     }

    //     // lemma shuffle_inv_peri_lemma<T>(
    //     //     a: seq<T>, c: seq<T>,
    //     //     ti: nat, i: nat, j: nat,
    //     //     view: rev_view)
    //     //     requires |a| == |b| == |c| == len.full;
    //     //     requires ti < |table|;
    //     //     requires bit_rev_table_inv();
    //     //     requires buffer_prefix_index(ti) < len.full;
    //     //     requires view.len == len;
    //     //     requires i == table[ti].0 < len.full;
    //     //     requires j == table[ti].1 < len.full;
    //     //     requires view.shuffle_inv(a, b, buffer_prefix_index(ti));
    //     //     requires c == b[i := b[j]][j := b[i]];
    //     // {

    //     // }


   
    // }
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

        //     reveal shuffle_inv();
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
        //     // ensures shuffle_inv(a, a, 0);
        // {
        //     reveal inital_finished_set();
        //     reveal shuffle_inv();

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

        // lemma shuffle_inv_lemma<T>(
        //     a: seq<T>, c: seq<T>,
        //     finished: set<nat>, 
        //     ti: nat, i: nat, j: nat)
        //     requires bit_rev_table_inv();
        //     requires |a| == |b| == |c| == len.full;
        //     requires ti < |table|;
        //     requires i < len.full;
        //     requires i == table[ti].0;
        //     requires j < len.full;
        //     requires j == table[ti].1;
        //     requires shuffle_inv(a, b, finished);
        //     requires c == b[i := b[j]][j := b[i]];
        // {
        //     var new_finished := finished + {i, j};
        //     reveal shuffle_inv();
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

