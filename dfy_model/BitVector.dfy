include "NativeTypes.dfy"
include "../otbn_model/lib/powers.dfy"

module CutomBitVector {
    import opened NativeTypes
    import opened powers

    type cbv = t: seq<uint2> | 0 < |t| <= UINT32_MAX witness [1]

    type cbv384 = t: cbv | |t| == 384

    type cbv768 = t: cbv | |t| == 768


    function to_nat(v: cbv) : nat
    {
        to_nat_aux(v, |v|)
    }

    function {:fuel 20} to_nat_aux(v: cbv, i: uint32) : nat
        decreases i;
        requires 0 <= i <= |v|;
    {
        if i == 0 then 0
        else to_nat_aux(v, i - 1) + pow2(i - 1) * v[i - 1]
    }

    function to_nat_alt(v: cbv) : nat
    {
        to_nat_alt_aux(v, 0)
    }

    function to_nat_alt_aux(v: cbv, i: uint32) : nat
        decreases |v| - i;
        requires 0 <= i <= |v|;
    {
        if i == |v| then 0
        else pow2(i) * v[i] + 2 * to_nat_alt_aux(v, i + 1)
    }

    function method lsb(v: cbv) : uint2
    {
        v[0]
    }

    function method msb(v: cbv) : uint2
    {
        v[|v| - 1]
    }

    lemma {:induction i} to_nat_prefix_lemma(v: cbv, v': cbv, i: nat)
        requires 0 <= i <= |v| && 0 <= i <= |v'|;
        requires v[..i] == v'[..i];
        ensures to_nat_aux(v, i) == to_nat_aux(v', i);
    {
        if i != 0 {
            assert to_nat_aux(v, i - 1) == to_nat_aux(v', i - 1);
        }
    }

    // lemma to_nat_aux_lemma(v: cbv)
    //     ensures to_nat_aux(v, |v|-1) == to_nat_aux(v[..|v|-1], |v|-1);
    // {
    //     to_nat_prefix_lemma(v, v);
    // }

    lemma to_nat_msb_lemma(v: cbv, l: uint32)
        requires l == |v|;
        ensures to_nat(v) == to_nat(v[..l-1]) + pow2(l-1) * msb(v);
    {
        if l != 1 {
            calc == {
                to_nat(v);
                to_nat_aux(v, l-1) + pow2(l-1) * v[l-1];
                {
                    to_nat_prefix_lemma(v, v[..l-1], l-1);
                }
                to_nat_aux(v[..l-1], l-1) + pow2(l-1) * msb(v);
            }
        }
    }

    method zero(l: uint32) returns (v: cbv)
        ensures |v| == l;
        ensures to_nat(v) == 0; 
    {
        assume false;
    }

    function method rshift(v: cbv, amt: uint32) : cbv
        requires amt < |v|;
    {
        v[amt..]
    }

    lemma {:induction amt} rshift_is_div(v: cbv, v1: cbv, amt: uint32)
        decreases amt;
        requires amt < |v|;
        requires v1 == rshift(v, amt);
        ensures to_nat(v1) == to_nat(v) / pow2(amt);
    {
        if amt == 0 {
            reveal power();
        } else {
            assert v1 == v[amt..];
            var l := |v| - amt;
            assert |v1| == l;

            var v2 := v[amt..];

            // rshift_is_div(v, v'', amt-1);
            // assert to_nat(v'') == to_nat(v) / pow2(amt-1);

            // calc == {
            //     to_nat(v');
            //     to_nat_aux(v', l);
            //     pow2(l-1) * v'[l-1] + to_nat_aux(v', l-1);
            // }


            // calc == {
            //     to_nat(v'');
            //     to_nat_aux(v'', l + 1);
            //     pow2(l) * v''[l] + to_nat_aux(v'', l);
            // }
            assume false;
        }
    }

    method concat(v1: cbv, v2: cbv) returns (v3: cbv)
    {
        return v1 + v2; 
    }

    method slice(v: cbv, lo: uint32, hi: uint32) returns (v': cbv)
        requires 0 <= lo < hi <= |v|;
        ensures v' == v[lo..hi];
    {
        v' := v[lo..hi];
    }

    // function method to_nat(v: cbv) : nat
    //     decreases v;
    // {
    //     if |v| == 0 then 0
    //     else v[0] + 2 * to_nat(v[1..])
    // }

    method cbv_test()
    {
        var a: cbv := [1, 1, 1, 0, 1];

        assert to_nat(a) == 23 by {
            reveal power();
        }

        a := slice(a, 1, 5);
        assert a == [1, 1, 0, 1];
        assert to_nat(a) == 11 by {
            reveal power();
        }

        a := rshift(a, 2);
        assert a == [0, 1];
    }
}