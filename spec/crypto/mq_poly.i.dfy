include "mq_poly.s.dfy"

module mq_poly_i(CMQ: ntt_param_s)
    refines mq_poly_s(CMQ)
{
    function {:fuel 1} list_fixed_pairs(val:nat, index:nat, len2: nat) : (r: seq<(nat, nat)>)
        requires index < len2
        ensures |r| == index + 1
        ensures forall i :: 0 <= i < |r| ==> r[i] == (val, i)
    {
        if index == 0 then 
            [(val, 0)]
        else
            list_fixed_pairs(val, index - 1, len2) + [(val, index)]
    }

    function list_all_pairs_aux(index:nat, len1: nat, len2: nat) : (r: seq<(nat, nat)>)
        requires index < len1
        requires 0 < len2
        ensures |r| == (index + 1) * len2
    {
        if index == 0 then 
            list_fixed_pairs(index, len2 - 1, len2)
        else
            var head := list_all_pairs_aux(index - 1, len1, len2); 
            var tail := list_fixed_pairs(index, len2 - 1, len2);
            calc {
                |head + tail|;
                |head| + |tail|;
                index * len2 + len2;
                index * len2 + 1 * len2;
                    { Mul.LemmaMulIsDistributiveAddOtherWayAuto(); }
                (index + 1) * len2; 
            }
            head + tail
    }

    lemma list_all_pairs_aux_lemma(index:nat, len1: nat, len2: nat, r: seq<(nat, nat)>)
        requires index < len1
        requires 0 < len2
        requires r == list_all_pairs_aux(index, len1, len2)
        ensures |r| == (index + 1) * len2 
        ensures forall i, j :: (0 <= i <= index && 0 <= j < len2) ==>
                        (0 <= (i*len2 + j) < |r| && r[i*len2 + j] == (i, j))
    {
        forall i, j | 0 <= i <= index && 0 <= j < len2 
            ensures 0 <= i*len2 + j < |r|
            ensures r[i*len2 + j] == (i, j)
        {
            // Lower-bound on index
            assert 0 <= i * len2 + j by { Mul.LemmaMulNonnegative(i, len2); }
            
            // Upper-bound on index
            calc {
                i * len2;
             <= { Mul.LemmaMulUpperBound(i, index, len2, len2); }
                index * len2;
            }

            calc {
                index * len2 + j;
            < index * len2 + len2;
                index * len2 + 1 * len2;
                    { Mul.LemmaMulIsDistributiveAddOtherWayAuto(); }
                (index + 1) * len2;
                |r|;
            }

            if index == 0 {
            } else {
                var head := list_all_pairs_aux(index - 1, len1, len2); 
                var tail := list_fixed_pairs(index, len2 - 1, len2);
                list_all_pairs_aux_lemma(index - 1, len1, len2, head);
                //var k := i * len2 + j;
                if i < index {
                    assert i*len2 + j < |head|;
                    calc {
                        r[i*len2 + j];
                        head[i*len2 + j];
                        (i, j);
                    }
                } else { // i == index
                    calc {
                        r[i*len2 + j];
                        tail[i*len2 + j - index*len2];
                        tail[j];
                        (i, j);
                    }
                }
            }
        }
    }

    function list_all_pairs(len1: nat, len2: nat) : (r: seq<(nat, nat)>)
        requires 0 < len1
        requires 0 < len2
        ensures |r| == len1 * len2
        ensures forall i, j :: 0 <= i < len1 && 0 <= j < len2 ==>
                0 <= (i*len2 + j) < |r| && r[i*len2 + j] == (i, j)
    {
        var r := list_all_pairs_aux(len1 - 1, len1, len2);
        list_all_pairs_aux_lemma(len1 - 1, len1, len2, r);
        r
    }

    function build_index_pairs(len1: nat, len2: nat, deg: nat): (r: seq<(nat, nat)>)
        requires 0 < len1 && 0 < len2
    {
        Seq.Filter((pair : (nat, nat)) => pair.0 + pair.1 == deg, list_all_pairs(len1, len2))
    }

    ghost method find_pair(k:nat, len1: nat, len2: nat, r: seq<(nat, nat)>) returns (i: nat, j: nat)
        requires k < |r|
        requires 0 < len1 && 0 < len2
        requires r == list_all_pairs(len1, len2)
        ensures i < len1 && j < len2
        ensures k == i*len2 + j
        ensures r[k] == (i, j)
    {
        i := 0;
        var k_candidate := 0;
        while i < len1
            invariant 0 <= i <= len1 
            invariant forall x, y :: 0 <= x < i && y < len2    ==> k != x*len2 + y
            invariant k_candidate == i*len2
            invariant forall z :: 0 <= z < k_candidate ==> z != k
        {
            j := 0;
            while j < len2 
                invariant 0 <= j <= len2
                invariant forall y :: 0 <= y < j ==> k != i*len2 + y
                invariant k_candidate == i*len2 + j
                invariant forall z :: 0 <= z < k_candidate ==> z != k
            {
                if k == i*len2 + j {
                    return;
                }
                j := j + 1;
                k_candidate := k_candidate + 1;
            }

            var i_new := i + 1;
            calc {
                k_candidate;
                i*len2 + len2;
                i*len2 + 1*len2;
                    { Mul.LemmaMulIsDistributiveAddOtherWay(len2, i, 1); }
                (i + 1) * len2;
                i_new * len2;
            }

            i := i + 1;
        }
    }

    lemma build_index_pairs_lemma(len1: nat, len2: nat, deg: nat, r: seq<(nat, nat)>)
        requires 0 < len1 && 0 < len2
        requires r == build_index_pairs(len1, len2, deg)
        ensures forall i: nat, j: nat :: (
            (i < len1 && j < len2 && i + j == deg)
                <==>
            exists_in_index_pairs(i, j, r))
    {
        var all_pairs := list_all_pairs(len1, len2);
        forall i: nat, j: nat | i < len1 && j < len2 && i + j == deg
            ensures exists_in_index_pairs(i, j, r) 
        {
            FilterProperties((pair : (nat, nat)) => pair.0 + pair.1 == deg, all_pairs, r);
            assert all_pairs[i *len2 + j] == (i, j);
            assert (exists k :: 0 <= k < |r| && r[k] == all_pairs[i*len2+j]);
        }
        forall i: nat, j: nat | exists_in_index_pairs(i, j, r) 
            ensures    i < len1 && j < len2 && i + j == deg
        {
            var k:nat :| 0 <= k < |r| && r[k] == (i, j);
            FilterProperties((pair : (nat, nat)) => pair.0 + pair.1 == deg, all_pairs, r);
            assert (exists m :: 0 <= m < |all_pairs| && r[k] == all_pairs[m]);
            var m :| 0 <= m < |all_pairs| && r[k] == all_pairs[m];
            var i, j := find_pair(m, len1, len2, all_pairs);
        }
    }

    lemma build_index_pairs_bound_lemma(len1: nat, len2: nat, deg: nat, r: seq<(nat, nat)>)
        requires r == index_pairs_wrapper(len1, len2, deg)
        ensures 
            forall i: nat, j: nat :: (
                (i < len1 && j < len2 && i + j == deg)
                    <==>
                exists_in_index_pairs(i, j, r))
    {
        if 0 < len1 && 0 < len2 {
            build_index_pairs_lemma(len1, len2, deg, r);
        } else if len1 == 0 {
            forall i: nat, j: nat | i < len1 && j < len2 && i + j == deg
                ensures exists_in_index_pairs(i, j, r) 
            {
            }

            forall i: nat, j: nat | exists_in_index_pairs(i, j, r) 
                ensures    i < len1 && j < len2 && i + j == deg
            {
                assert false;
            }
        } else if len2 == 0 {
        }
    }

    predicate exists_match<T>(s:seq, val:T)
    {
        exists j :: 0 <= j < |s| && val == s[j]
    }

    lemma FilterProperties<T>(f: (T ~> bool), s: seq<T>, result: seq<T>)
        requires forall i :: 0 <= i < |s| ==> f.requires(s[i])
        requires result == Seq.Filter(f, s)
        ensures |result| <= |s|
        ensures forall i: nat {:trigger result[i]} :: i < |result| && f.requires(result[i]) ==> f(result[i])
        ensures forall i: nat :: i < |s| && f(s[i]) ==> exists_match(result, s[i]) 
        ensures forall i: nat :: i < |result| ==> exists_match(s, result[i])
    {
        if |s| == 0 {
            return;
        }

        forall i: nat | i < |s| && f(s[i]) 
            ensures exists_match(result, s[i]) 
        {
            reveal Filter();
            if i == 0 {
                assert result[0] == s[i];
            } else {
                if f(s[0]) {
                    FilterProperties(f, s[1..], result[1..]);
                } else {
                    FilterProperties(f, s[1..], result);
                }
            }
        }
        
        forall i: nat | i < |result| 
            ensures exists_match(s, result[i])
        {
            reveal Filter();
            if f(s[0]) {
                FilterProperties(f, s[1..], result[1..]);
            } else {
                FilterProperties(f, s[1..], result);
            }
        }
    }

    function index_pairs_wrapper(len1: nat, len2: nat, deg: nat): (r: seq<(nat, nat)>)
    {
        if 0 < len1 && 0 < len2 then
            build_index_pairs(len1, len2, deg)
        else
            []
    }

    function index_pairs(len1: nat, len2: nat, deg: nat): (r: seq<(nat, nat)>)
        // requires deg < len1 + len2 - 1;
        // ensures forall j: nat, k: nat :: (
        //     (j < len1 && k < len2 && j + k == deg)
        //         <==>
        //     exists_in_index_pairs(j, k, r));
    {
        var r := index_pairs_wrapper(len1, len2, deg);
        build_index_pairs_bound_lemma(len1, len2, deg, r);
        r
    }

    function poly_offset_terms(a: seq<elem>, x: elem, k: nat): seq<elem>
    {
        seq(|a|, i requires 0 <= i < |a| => mqmul(a[i], mqpow(x, i + k)))
    }

    function method {:opaque} even_indexed_items<T>(a: seq<T>, len: pow2_t): (r: seq<T>)
        requires |a| == len.full;
        ensures |r| == len.full / 2;
    {
        pow2_basics_lemma(len);
        seq(len.full/2, n requires 0 <= n < len.full/2 => a[n * 2])
    }

    function method {:opaque} odd_indexed_items<T>(a: seq<T>, len: pow2_t): (r: seq<T>)
        requires |a| == len.full;
        ensures |r| == len.full / 2;
    {
        pow2_basics_lemma(len);
        seq(len.full/2, n requires 0 <= n < len.full/2 => a[n * 2 + 1])
    }

    function method {:opaque} merge_even_odd_indexed_items<T>(a: seq<T>, b: seq<T>, len: pow2_t): (r: seq<T>)
        requires |a| == |b| == len.full;
        ensures |r| == pow2_double(len).full;
        ensures even_indexed_items(r, pow2_double(len)) == a;
        ensures odd_indexed_items(r, pow2_double(len)) == b;
    {
        pow2_basics_lemma(len);
        var new_len := pow2_double(len);
        var r := seq(new_len.full, n requires 0 <= n < new_len.full => 
            if n % 2 == 0 then a[n/2] else b[n/2]);
        assert even_indexed_items(r, new_len) == a by {
            reveal even_indexed_items();
        }
        assert odd_indexed_items(r, new_len) == b by {
            reveal odd_indexed_items();
        }
        r
    }

    lemma mqsum2_lemma(s: seq<elem>)
        requires |s| == 2;
        ensures mqsum(s) == mqadd(s[0], s[1])
    {
        assert mqsum(s) == mqadd(s[0], mqsum(s[1..]));
        LemmaSmallMod(s[1], Q);
    }

    lemma mqadd_associates(x: elem, y: elem, z: elem)
        ensures mqadd(x, mqadd(y, z)) == mqadd(mqadd(x, y), z)
    {
        calc {
            mqadd(x, mqadd(y, z));
            (x + ((y + z) % Q)) % Q;
                { LemmaAddModNoop(x, y+z, Q); }
            (x + (y + z)) % Q;
                { assert x + (y + z) == (x + y) + z; }
            ((x + y) + z) % Q;
                { LemmaAddModNoop(x+y, z, Q); }
            (((x + y) % Q) + z) % Q;
            mqadd(mqadd(x, y), z);
        }
    }

    lemma mqadd_reassociate(a: elem, b: elem, y: elem, z: elem)
        ensures mqadd(mqadd(a, b), mqadd(y, z)) 
             == mqadd(mqadd(a, y), mqadd(b, z)) 
    {
        calc {
            mqadd(mqadd(a, b), mqadd(y, z));
                { mqadd_associates(a, b, mqadd(y, z)); }
            mqadd(a, mqadd(b, mqadd(y, z)));
                { mqadd_associates(b, y, z); }
            mqadd(a, mqadd(mqadd(b, y), z));
                { assert mqadd(b, y) == mqadd(y, b); }
            mqadd(a, mqadd(mqadd(y, b), z));
                { mqadd_associates(y, b, z); }
            mqadd(a, mqadd(y, mqadd(b, z)));
                { mqadd_associates(a, y, mqadd(b, z)); }
            mqadd(mqadd(a, y), mqadd(b, z));
        }
    }

    lemma mqsum_adds(s1: seq<elem>, s2: seq<elem>) 
        ensures mqsum(s1 + s2) == mqadd(mqsum(s1), mqsum(s2))
    {
        if |s1| == 0 {
            assert mqsum(s1) == 0;
            assert s1 + s2 == s2;
            LemmaSmallMod(mqsum(s2), Q);
        } else {
            calc {
                mqsum(s1 + s2);
                    { assert (s1 + s2)[1..] == s1[1..] + s2; }
                mqadd(s1[0], mqsum(s1[1..] + s2));
                    { mqsum_adds(s1[1..], s2); }
                mqadd(s1[0], mqadd(mqsum(s1[1..]), mqsum(s2)));
                    { mqadd_associates(s1[0], mqsum(s1[1..]), mqsum(s2)); }
                mqadd(mqadd(s1[0], mqsum(s1[1..])), mqsum(s2));
                mqadd(mqsum(s1), mqsum(s2));
            }
        }
    }

    lemma mqmul_commutes(a: elem, b: elem)
        ensures mqmul(a, b) == mqmul(b, a);
    {
        LemmaMulIsCommutative(a, b);
    }

    lemma mqmul_distributes(x: elem, y: elem, z: elem)
        ensures mqmul(x, mqadd(y, z)) == mqadd(mqmul(x, y), mqmul(x, z))
    {
        calc {
            mqmul(x, mqadd(y, z));
            (x * ((y + z) % Q)) % Q;
                { LemmaMulModNoopGeneral(x, y+z, Q); }
            (x * (y + z)) % Q;
                { LemmaMulIsDistributiveAdd(x, y, z); }
            (x * y + x * z) % Q;
                { LemmaAddModNoop(x*y, x*z, Q); }
            (((x * y) % Q) + ((x * z) % Q)) % Q;
            (mqmul(x, y) + mqmul(x, z)) % Q;
            mqadd(mqmul(x, y), mqmul(x, z));
        }
    }

    lemma mqmul_associates(x: elem, y: elem, z: elem)
        ensures mqmul(x, mqmul(y, z)) == mqmul(mqmul(x, y), z)
    {
        calc {
            mqmul(x, mqmul(y, z));
            (x * ((y * z) % Q)) % Q;
                { LemmaMulModNoopGeneral(x, y*z, Q); }
            (x * (y * z)) % Q;
                { LemmaMulIsAssociative(x, y, z); }
            ((x * y) * z) % Q;
                { LemmaMulModNoopGeneral(x*y, z, Q); }
            (((x * y) % Q) * z) % Q;
            mqmul(mqmul(x, y), z);
        }
    }

    lemma mqpow_muls(x: elem, b: nat, c: nat)
        ensures b * c >= 0;
        ensures mqpow(mqpow(x, b), c) == mqpow(x, b * c);
    {
        calc == {
            mqpow(mqpow(x, b), c);
            Pow(Pow(x, b) % Q, c) % Q;
            {
                LemmaPowModNoop(Pow(x, b), c, Q);
            }
            Pow(Pow(x, b), c) % Q;
            {
                LemmaPowMultiplies(x, b, c);
            }
            Pow(x, b * c) % Q;
            mqpow(x, b * c);
        }
        LemmaMulNonnegative(b, c);
    }

    lemma mqpow_adds(x: elem, b: nat, c: nat)
        ensures mqmul(mqpow(x, b), mqpow(x, c)) == mqpow(x, b + c);
    {
        calc == {
            mqmul(mqpow(x, b), mqpow(x, c));
            ((Pow(x, b) % Q) * (Pow(x, c) % Q)) % Q;
            {
                LemmaMulModNoopGeneral(Pow(x, b), Pow(x, c), Q);
            }
            (Pow(x, b) * Pow(x, c)) % Q;
            {
                LemmaPowAdds(x, b, c);
            }
            Pow(x, b + c) % Q;
            mqpow(x, b + c);
        }
    }

    lemma mqpow_group(x:elem, offset:nat)
        ensures mqpow(mqmul(x, x), offset) == mqpow(x, 2*offset)
        ensures mqmul(x, mqpow(x, 2*offset)) == mqpow(x, 1+2*offset)
    {
        calc {
        mqpow(mqmul(x, x), offset);
        Pow((x * x) % Q, offset) % Q;
            { LemmaPowModNoop(x*x, offset, Q); }
        Pow(x * x, offset) % Q;
            { reveal Pow(); assert Pow(x, 2) == x * x; }
        Pow(Pow(x, 2), offset) % Q;
            { LemmaPowMultiplies(x, 2, offset); }
        Pow(x, 2*offset) % Q;
        mqpow(x, 2*offset);
        }
        
        calc {
        mqmul(x, mqpow(x, 2*offset));
        mqmul(x, Pow(x, 2*offset) % Q);
        (x * (Pow(x, 2*offset) % Q)) % Q;
            { LemmaMulModNoopGeneral(x, Pow(x, 2*offset), Q); }
        (x * Pow(x, 2*offset)) % Q;
            { reveal Pow(); }
        Pow(x, 1+2*offset) % Q;
        mqpow(x, 1+2*offset);
        }
    }

    lemma poly_eval_base_lemma(a: seq<elem>, x: elem)
        requires |a| == 1;
        ensures poly_eval(a, x) == a[0];
    {
        reveal poly_eval();
        calc == {
            poly_eval(a, x);
            mqsum(poly_terms(a, x));
            mqadd(poly_terms(a, x)[0], 0);
            {
                LemmaSmallMod(poly_terms(a, x)[0], Q);
            }
            poly_terms(a, x)[0];
            mqmul(a[0], mqpow(x, 0));
            {
                LemmaPow0Auto();
            }
            mqmul(a[0], 1);
            {
                LemmaMulBasics(a[0]);
            }
            a[0] % Q;
            {
                LemmaSmallMod(a[0], Q);
            }
            a[0];
        }
    }

    function {:opaque} poly_eval_offset(a: seq<elem>, x: elem, offset: nat): elem
    {
        mqsum(poly_offset_terms(a, x, offset))
    }

    lemma poly_eval_offset_zero_lemma(a: seq<elem>, x: elem)
        ensures poly_eval(a, x) == poly_eval_offset(a, x, 0);
    {
        reveal poly_eval();
        reveal poly_eval_offset();

        var left := seq(|a|, i requires 0 <= i < |a| => mqmul(a[i], mqpow(x, i)));
        var right := seq(|a|, i requires 0 <= i < |a| => mqmul(a[i], mqpow(x, i + 0)));
        assert left == right;
    }

    lemma poly_eval_split_rec_lemma(a: seq<elem>, 
        a_e: seq<elem>, a_o: seq<elem>, len: pow2_t, x: elem, offset: nat)
        requires |a| == len.full >= 2;
        requires a_e == even_indexed_items(a, len)
        requires a_o == odd_indexed_items(a, len)
        ensures var sqr := mqmul(x, x);
            poly_eval_offset(a, x, 2*offset)
                == 
            mqadd(poly_eval_offset(a_e, sqr, offset), mqmul(x, poly_eval_offset(a_o, sqr, offset)));
        decreases |a|;
    {
        var sqr := mqmul(x, x);

        if |a| == 2 {
            assert a_e == [a[0]] by {
                reveal even_indexed_items();
            }
            assert a_o == [a[1]] by {
                reveal odd_indexed_items();
            }

            calc == {
                poly_eval_offset(a, x, 2*offset);
                    { reveal poly_eval_offset(); }
                mqsum(poly_offset_terms(a, x, 2*offset));
                    {
                    assert poly_offset_terms(a, x, 2*offset) ==
                            [mqmul(a[0], mqpow(x, 2*offset)), 
                             mqmul(a[1], mqpow(x, 1 + 2*offset))];
                    }
                mqsum([mqmul(a[0], mqpow(x, 2*offset)), 
                mqmul(a[1], mqpow(x, 1 + 2*offset))]);
                    { mqsum2_lemma([mqmul(a[0], mqpow(x, 2*offset)), mqmul(a[1], mqpow(x, 1 + 2*offset))]); }
                mqadd(mqmul(a[0], mqpow(x, 2*offset)), 
                         mqadd(mqmul(a[1], mqpow(x, 1 + 2*offset)), 0));
                mqadd(mqmul(a[0], mqpow(x, 2*offset)), 
                         mqmul(a[1], mqpow(x, 1 + 2*offset)));
                    { mqpow_group(x, offset); }
                mqadd(mqmul(a[0], mqpow(sqr, offset)), 
                        mqmul(a[1], mqmul(x, mqpow(sqr, offset)))); 
                    { mqmul_associates(a[1], x, mqpow(sqr, offset)); }
                mqadd(mqmul(a[0], mqpow(sqr, offset)), 
                        mqmul(mqmul(a[1], x), mqpow(sqr, offset))); 
                mqadd(mqmul(a[0], mqpow(sqr, offset)), 
                        mqmul(mqmul(x, a[1]), mqpow(sqr, offset))); 
                    { mqmul_associates(x, a[1], mqpow(sqr, offset)); }
                mqadd(mqmul(a[0], mqpow(sqr, offset)), 
                        mqmul(x, mqmul(a[1], mqpow(sqr, offset)))); 
                mqadd(mqsum([mqmul(a[0], mqpow(sqr, offset))]), 
                        mqmul(x, mqsum([mqmul(a[1], mqpow(sqr, offset))]))); 
                mqadd(mqsum([mqmul(a_e[0], mqpow(sqr, offset))]), 
                        mqmul(x, mqsum([mqmul(a_o[0], mqpow(sqr, offset))]))); 
                    { 
                    reveal poly_eval_offset(); 
                    assert poly_offset_terms(a_e, sqr, offset) ==
                             [mqmul(a_e[0], mqpow(sqr, offset))];
                    assert poly_offset_terms(a_o, sqr, offset) ==
                             [mqmul(a_o[0], mqpow(sqr, offset))];
                    }
                mqadd(poly_eval_offset(a_e, sqr, offset), mqmul(x, poly_eval_offset(a_o, sqr, offset)));
            }
            return;
        }

        var apowers := poly_offset_terms(a, x, 2*offset);
        var epowers := poly_offset_terms(a_e, sqr, offset);
        var opowers := poly_offset_terms(a_o, sqr, offset);

        calc {
            Pow2(0);
                { LemmaPow2(0); }
            Pow(2, 0);
                { LemmaPow0(2); }
            1;
        }

        var half := pow2_half(len);
        var quarter := pow2_half(half);

        assert apowers[half.full..]     == poly_offset_terms(a[half.full..], x, half.full + 2*offset);
        assert epowers[quarter.full..] == poly_offset_terms(a_e[quarter.full..], sqr, quarter.full + offset);
        assert opowers[quarter.full..] == poly_offset_terms(a_o[quarter.full..], sqr, quarter.full + offset);

        assert apowers[..half.full]     == poly_offset_terms(a[..half.full], x, 2*offset);
        assert epowers[..quarter.full] == poly_offset_terms(a_e[..quarter.full], sqr, offset);
        assert opowers[..quarter.full] == poly_offset_terms(a_o[..quarter.full], sqr, offset);

        assert (quarter.full + offset) * 2 == half.full + 2*offset;

        calc {
            poly_eval_offset(a, x, 2*offset);
                { reveal poly_eval_offset(); }
            mqsum(apowers);
                { 
                    mqsum_adds(apowers[..half.full], apowers[half.full..]);    
                    assert apowers == apowers[..half.full] + apowers[half.full..]; 
                }
            mqadd(mqsum(apowers[..half.full]), mqsum(apowers[half.full..]));
                { reveal poly_eval_offset(); }
            mqadd(poly_eval_offset(a[..half.full], x, 2*offset), poly_eval_offset(a[half.full..], x, half.full + 2*offset));
                { 
                    reveal even_indexed_items();
                    reveal odd_indexed_items();
                    assert even_indexed_items(a[..half.full], half) == a_e[..quarter.full];
                    assert    odd_indexed_items(a[..half.full], half) == a_o[..quarter.full];
                    poly_eval_split_rec_lemma(a[..half.full], a_e[..quarter.full], a_o[..quarter.full], half, x, offset); 
                }
            mqadd(mqadd(poly_eval_offset(a_e[..quarter.full], sqr, offset), mqmul(x, poly_eval_offset(a_o[..quarter.full], sqr, offset))), poly_eval_offset(a[half.full..], x, half.full + 2*offset));
                { 
                    reveal even_indexed_items();
                    reveal odd_indexed_items();
                    assert even_indexed_items(a[half.full..], half) == a_e[quarter.full..];
                    assert    odd_indexed_items(a[half.full..], half) == a_o[quarter.full..];
                    poly_eval_split_rec_lemma(a[half.full..], a_e[quarter.full..], a_o[quarter.full..], half, x, quarter.full + offset); 
                }
            mqadd(mqadd(poly_eval_offset(a_e[..quarter.full], sqr, offset), mqmul(x, poly_eval_offset(a_o[..quarter.full], sqr, offset))),
                    mqadd(poly_eval_offset(a_e[quarter.full..], sqr, quarter.full + offset), mqmul(x, poly_eval_offset(a_o[quarter.full..], sqr, quarter.full + offset))));
                { mqadd_reassociate(poly_eval_offset(a_e[..quarter.full], sqr, offset), mqmul(x, poly_eval_offset(a_o[..quarter.full], sqr, offset)),
                                        poly_eval_offset(a_e[quarter.full..], sqr, quarter.full + offset), mqmul(x, poly_eval_offset(a_o[quarter.full..], sqr, quarter.full + offset))); }
            mqadd(mqadd(poly_eval_offset(a_e[..quarter.full], sqr, offset), poly_eval_offset(a_e[quarter.full..], sqr, quarter.full + offset)),
                    mqadd(mqmul(x, poly_eval_offset(a_o[..quarter.full], sqr, offset)), mqmul(x, poly_eval_offset(a_o[quarter.full..], sqr, quarter.full + offset))));
                { mqmul_distributes(x, poly_eval_offset(a_o[..quarter.full], sqr, offset), poly_eval_offset(a_o[quarter.full..], sqr, quarter.full + offset)); }
            mqadd(mqadd(poly_eval_offset(a_e[..quarter.full], sqr, offset), poly_eval_offset(a_e[quarter.full..], sqr, quarter.full + offset)), 
                    mqmul(x, mqadd(poly_eval_offset(a_o[..quarter.full], sqr, offset), poly_eval_offset(a_o[quarter.full..], sqr, quarter.full + offset)))); 
                { reveal poly_eval_offset(); }
            mqadd(mqadd(mqsum(epowers[..quarter.full]), mqsum(epowers[quarter.full..])), mqmul(x, mqadd(mqsum(opowers[..quarter.full]), mqsum(opowers[quarter.full..]))));
                { 
                    mqsum_adds(epowers[..quarter.full], epowers[quarter.full..]);    
                    assert epowers == epowers[..quarter.full] + epowers[quarter.full..]; 
                    mqsum_adds(opowers[..quarter.full], opowers[quarter.full..]);    
                    assert opowers == opowers[..quarter.full] + opowers[quarter.full..]; 
                }
            mqadd(mqsum(epowers), mqmul(x, mqsum(opowers)));
                { reveal poly_eval_offset(); }
            mqadd(poly_eval_offset(a_e, sqr, offset), mqmul(x, poly_eval_offset(a_o, sqr, offset)));
        }
    }

    lemma poly_eval_split_lemma(a: seq<elem>, 
        a_e: seq<elem>, a_o: seq<elem>, len: pow2_t, x: elem)
        requires |a| == len.full >= 2;
        requires a_e == even_indexed_items(a, len)
        requires a_o == odd_indexed_items(a, len)
        ensures var sqr := mqmul(x, x);
            poly_eval(a, x)
                == 
            mqadd(poly_eval(a_e, sqr), mqmul(x, poly_eval(a_o, sqr)));
        decreases |a|;
    {
        poly_eval_split_rec_lemma(a, a_e, a_o, len, x, 0); 

        var sqr := mqmul(x, x);
        assert poly_eval_offset(a, x, 0)
                == 
            mqadd(poly_eval_offset(a_e, sqr, 0), mqmul(x, poly_eval_offset(a_o, sqr, 0)));

        poly_eval_offset_zero_lemma(a, x);
        poly_eval_offset_zero_lemma(a_e, sqr);
        poly_eval_offset_zero_lemma(a_o, sqr);
    }

    function method {:axiom} inverse_ntt_scaling_table(): (t: seq<elem>)
        ensures |t| == N.full;

    lemma {:axiom} inverse_ntt_scaling_table_axiom(i: nat)
        requires i < N.full;
        ensures inverse_ntt_scaling_table()[i] == 
            mqmul(mqmul(mqpow(CMQ.PSI_INV, i), CMQ.N_INV), CMQ.R);
}
