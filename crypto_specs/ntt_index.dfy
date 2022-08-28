include "bin_seq.i.dfy"
include "pow2.s.dfy"

module ntt_index {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul

    import opened pow2_s
    import opened bin_seq_i

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
        reveal Pow2();

        if len.exp < 2 {
            assert len.exp == 0 || len.exp == 1;
            // not the best proof
            reveal Pow();
            assert false;
        }

        var zero := FromNatWithLen(0, len.exp);
        LemmaSeqZero(zero);
        var zrs := Reverse(zero);
        assert zrs == SeqZero(len.exp);

        var one := FromNatWithLen(1, len.exp);
        var ors := Reverse(one);

        if ors == one {
            BitSelModEquivalence(one, 0);
            LemmaPow0(2);
            assert one[0] == 1;
            assert ors[len.exp - 1] == 1;
            BitSelModEquivalence(ors, len.exp - 1);
            var temp := Pow(2, len.exp - 1);
            assert temp > 1 by {
                LemmaPowStrictlyIncreases(2, 0, len.exp - 1);
            }
            calc == {
                ors[len.exp - 1];
                (1 / temp) % 2;
                {
                    LemmaDivDecreases(1, temp);
                    assert (1 / temp) >= 0 by {
                        LemmaDivBasicsAuto();
                    }
                    assert (1 / temp) == 0;
                }
                0 % 2;
                0;
            }
            assert false;
        }

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
        var len := bound.exp;

        if rsi == rsj {
            forall k | 0 <= k < len
                ensures si[k] == sj[k];
            {
                calc {
                    si[k];
                    rsi[len - k - 1];
                    rsj[len - k - 1];
                    sj[k];
                }
            }
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
    
    predicate {:opaque} is_bit_rev_shuffle(a: seq<nat>, b: seq<nat>, len: pow2_t)
    {
        && (|a| == |b| == len.full)
        && (forall i | 0 <= i < len.full ::
            a[i] == b[bit_rev_int(i, len)])
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

    lemma bit_rev_shuffle_symmetric(a: seq<nat>, b: seq<nat>, len: pow2_t)
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

    function init_finished(len: pow2_t): set<nat>
        requires len.full >= 4;
    {
        set bi: nat | (0 <= bi < len.full && bi == bit_rev_int(bi, len)) :: bi
    }

    function {:opaque} init_unfinished(len: pow2_t): set<nat>
        requires len.full >= 4;
    {
        set bi: nat | (0 <= bi < len.full && bi != bit_rev_int(bi, len)) :: bi
    }

    datatype rev_view = rev_view(
        b: seq<nat>,
        finished: set<nat>,
        unfinished: set<nat>,
        len: pow2_t,
        ti: nat)
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

        predicate index_is_shuffled(a: seq<nat>, bi: nat)
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

        predicate {:opaque} finished_shuffle_inv(a: seq<nat>)
            requires |a| == len.full;
            requires rev_view_wf()
        {
            && reveal rev_view_wf();
            && (forall bi | bi in finished ::(
                && bit_rev_int(bi, len) in finished
                && index_is_shuffled(a, bi)))
        }

        predicate {:opaque} unfinished_shuffle_inv(a: seq<nat>)
            requires |a| == len.full;
            requires rev_view_wf()
        {
            && reveal rev_view_wf();
            && (forall bi | bi in unfinished :: (
                && bit_rev_int(bi, len) in unfinished
                && bi != bit_rev_int(bi, len)
                && a[bi] == b[bi]))
        }

        predicate {:opaque} shuffle_prefix_inv()
            requires rev_view_wf();
        {
            var split_index := get_split_index_wrap();
            && (forall bi | 0 <= bi < split_index :: bi in finished)
        }

        predicate shuffle_inv(a: seq<nat>)
            requires |a| == len.full;
            ensures shuffle_inv(a) ==> rev_view_wf();
        {
            && rev_view_wf()
            && finished_shuffle_inv(a)
            && unfinished_shuffle_inv(a)
            && shuffle_prefix_inv()
            && (2 * ti) == |init_unfinished(len)| - |unfinished|
        }

        lemma split_index_unfinished_lemma(a: seq<nat>)
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

        static function {:opaque} init_rev_view(a: seq<nat>, len: pow2_t): (r: rev_view)
            requires |a| == len.full >= 4;
            ensures r.len == len;
            ensures r.rev_view_wf();
            ensures r.ti == 0;
            ensures r.b == a;
        {    
            var finished := init_finished(len);
            var unfinished := init_unfinished(len);
            var r := rev_view(a, finished, unfinished, len, 0);
            assert 2 * r.ti == 0;
            assert r.rev_view_wf() by {
                reveal init_unfinished();
                reveal r.rev_view_wf();
            }
            r
        }

        lemma init_unfinished_lemma(a: seq<nat>, len: pow2_t)
            requires |a| == len.full >= 4;
            requires this == init_rev_view(a, len);
            ensures 0 in finished;
            ensures 1 in unfinished;
            ensures |unfinished| != 0;
            ensures get_split_index() == 1;
        {
            reveal init_unfinished();
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

        lemma shuffle_inv_pre_lemma(a: seq<nat>, len: pow2_t)
            requires |a| == len.full >= 4;
            requires this == init_rev_view(a, len);
            ensures this.shuffle_inv(a);
        {
            bit_rev_int_basics_lemma(len);
            reveal init_unfinished();

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

            assert 2 * ti == |init_unfinished(len)| - |unfinished| by {
                reveal init_rev_view();
            }
        }

        function next_rev_buffer(): (c: seq<nat>)
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

        function next_rev_view(a: seq<nat>): (r: rev_view)
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
                    len, ti + 1);
                assert r.rev_view_wf() by {
                    reveal r.rev_view_wf();
                }
                r
            else
                this
        }

        lemma shuffle_inv_peri_lemma(a: seq<nat>, next: rev_view)
            requires |a| == len.full;
            requires shuffle_inv(a);
            requires 2 * ti < |init_unfinished(len)|;
            requires next == next_rev_view(a);
            ensures next.shuffle_inv(a);
        {
            assert |unfinished| != 0;

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

            assert 2 * next.ti == |init_unfinished(len)| - |next.unfinished| by {
                assert sbj in unfinished;
                assert rsbj in unfinished;
                assert sbj != rsbj by {
                    reveal unfinished_shuffle_inv();
                }
                LemmaSetSubtractTwoCardinality(unfinished, sbj, rsbj);
                assert |next.unfinished| == |unfinished| - 2;
            }
        }

        lemma shuffle_inv_post_lemma(a: seq<nat>)
            requires |a| == len.full;
            requires shuffle_inv(a);
            // requires get_split_index_wrap() == len.full;
            requires 2 * ti == |init_unfinished(len)|; 
            ensures is_bit_rev_shuffle(a, b, len);
        {
            assert |unfinished| == 0;
            assert finished == set bi: nat | (0 <= bi < len.full) :: bi by {
                reveal rev_view_wf();
            }

            assert is_bit_rev_shuffle(a, b, len) by {
                reveal is_bit_rev_shuffle();
                reveal finished_shuffle_inv();
            }
        }
    }

    function build_view(a: seq<nat>, i: nat, len: pow2_t): (r: rev_view)
        requires |a| == len.full >= 4;
        requires i * 2 <= |init_unfinished(len)|
        ensures len == r.len;
        ensures r.shuffle_inv(a);
        ensures r.ti == i;
        ensures i * 2 != |init_unfinished(len)| ==> |r.unfinished| != 0;
    {
        var r := if i == 0 then 
            rev_view.init_rev_view(a, len)
        else
            build_view(a, i - 1, len).next_rev_view(a);
            assert r.shuffle_inv(a) by {
                if i == 0 {
                    r.shuffle_inv_pre_lemma(a, len);
                } else if 2 * i <= |init_unfinished(len)| {
                    build_view(a, i - 1, len).shuffle_inv_peri_lemma(a, r);
                }
            }
            r
    }

    predicate {:opaque} table_wf(table: seq<(nat, nat)>, a: seq<nat>, len: pow2_t)
        requires |a| == len.full >= 4;
    {
        && 2 * |table| == |init_unfinished(len)|
        && (forall i | 0 <= i < |table| :: (
            && table[i].0 == build_view(a, i, len).get_split_index())
            && table[i].1 == bit_rev_int(table[i].0, len))
    }

    method bit_rev(a: seq<nat>, len: pow2_t, table: seq<(nat, nat)>)
        returns (b: seq<nat>)
        requires |a| == len.full >= 4;
        requires table_wf(table, a, len);
        ensures |b| == len.full;
        ensures is_bit_rev_shuffle(a, b, len);
    {
        b := a;
        var ti := 0;
        reveal table_wf();
        ghost var view := rev_view.init_rev_view(a, len);
        view.shuffle_inv_pre_lemma(a, len);

        while ti < |table|
            invariant ti * 2 <= |init_unfinished(len)|;
            invariant view == build_view(a, ti, len);
            invariant view.b == b;
        {
            var prev_b := b;

            var i := table[ti].0;
            var j := table[ti].1;

            var temp := b[i];
            b := b[i := b[j]];
            b := b[j := temp];

            var next_view := view.next_rev_view(a);
            assert b == view.next_rev_buffer();
            view.shuffle_inv_peri_lemma(a, next_view);
    
            view := next_view;
            ti := ti + 1;
        }

        view.shuffle_inv_post_lemma(a);
    }
    
}