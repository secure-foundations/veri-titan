include "../otbn_model/lib/powers.dfy"
include "NativeTypes.dfy"

module CutomBitVector {
    import opened powers
    import opened NativeTypes

    // lsb: t[0], msb: t[|t| - 1]
    type cbv = t: seq<uint1> | 0 < |t| < 0x100000000 witness [1]

    method cbv_print(n: string, v: cbv)
    {
        print "[INPUT]", n, ":", |v|, ":";
        var i := 0;
        while i < |v|
            decreases |v| - i;
        {
            print(v[i]);
            i := i + 1;
        }
        print("\n");
    }

    function method to_nat(v: cbv) : nat
    {
        to_nat_aux(v, |v|)
    }

    // function {:fuel 20} to_nat_aux(v: cbv, i: uint32) : nat
    function method to_nat_aux(v: cbv, i: uint32) : nat
        decreases i;
        requires 0 <= i <= |v|;
    {
        if i == 0 then 0
        else to_nat_aux(v, i - 1) + pow2(i - 1) * v[i - 1]
    }

    function method from_nat(n: nat, l: nat) : cbv
        decreases l;
    {
        if l == 0 then []
        else if n % 2 == 1 then [1] + from_nat(n / 2, l - 1) 
        else [0] + from_nat(n / 2, l -1)
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

    lemma to_nat_equivalent_lemma(v: cbv)
        ensures to_nat(v) == to_nat_alt(v);
    {
        if |v| == 1 {
            calc == {
                to_nat(v);
                pow2(0) * v[0];
                to_nat_alt_aux(v, 0);
            }
        } else {
            var l := |v|;

            calc == {
                to_nat_alt(v);
                to_nat_alt_aux(v, 0);
                pow2(0) * v[0] + 2 * to_nat_alt_aux(v, 1);
                {
                    reveal power();
                }
                v[0] + 2 * to_nat_alt_aux(v, 1);
                {
                    assume false;
                }
                v[0] + 2 * to_nat_alt_aux(v[1..], 0);
                v[0] + 2 * to_nat_alt(v[1..]);
                {
                    to_nat_equivalent_lemma(v[1..]);
                }
                v[0] + 2 * to_nat(v[1..]);
                {
                    to_nat_lsb_lemma(v);
                }
                to_nat(v);
            }
            assert to_nat_alt(v) == to_nat(v);
        }
    } 

    function method lsb(v: cbv) : uint1
    {
        v[0]
    }

    function method msb(v: cbv) : uint1
    {
        v[|v| - 1]
    }

    lemma to_nat_msb_lemma(v: cbv, l: uint32)
        requires l == |v|;
        ensures to_nat(v) == to_nat(v[..l-1]) + pow2(l-1) * msb(v);
    {
        if l == 1 {
            calc == {
                to_nat(v);
                to_nat_aux(v, 0) + pow2(0) * v[0];
                pow2(0) * v[0];
            }
        } else {
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

    lemma to_nat_lsb_lemma(v: cbv)
        decreases v;
        ensures to_nat(v) == v[0] + 2 * to_nat(v[1..]);
    {
        var l := |v|;
        if l != 1 {
            calc == {
                to_nat(v);
                to_nat_aux(v, l - 1) + pow2(l - 1) * v[l - 1];
                {
                    to_nat_prefix_lemma(v, v[..l-1], l-1);
                }
                to_nat_aux(v[..l-1], l-1) + pow2(l - 1) * v[l - 1];
                {
                    to_nat_lsb_lemma(v[..l-1]);
                }
                v[0] + 2 * to_nat(v[1..l-1]) + pow2(l - 1) * v[l - 1];
                {
                    assert 2 * pow2(l - 2) == pow2(l - 1) by {
                        reveal power();
                    }
                }
                v[0] + 2 * (to_nat(v[1..l-1]) + pow2(l - 2) * v[l - 1]);
                v[0] + 2 * (to_nat_aux(v[1..l-1], l -2) + pow2(l - 2) * v[l - 1]);
                {
                    to_nat_prefix_lemma(v[1..l-1], v[1..], l-2);
                }
                v[0] + 2 * (to_nat_aux(v[1..], l - 2) + pow2(l - 2) * v[l - 1]);
                v[0] + 2 * to_nat(v[1..]);
            }
            assert to_nat(v) == v[0] + 2 * to_nat(v[1..]);
        } else {
            calc == {
                to_nat(v);
                to_nat_aux(v, 0) + pow2(0) * v[0];
                {
                    reveal power();
                }
                v[0];
            }
        }
    }

    lemma {:induction i} to_nat_split_lemma(v: cbv, i: uint32)
        requires 0 < i < |v|;
        requires |v| > 1;
        ensures to_nat(v) == to_nat(v[..i]) + to_nat(v[i..]) * pow2(i);
    {
        if i == 1 {
            assert to_nat(v) == v[0] + 2 * to_nat(v[1..]) by {
                to_nat_lsb_lemma(v);
            }
            reveal power();
        } else {
            calc == {
                to_nat(v);
                {
                    to_nat_split_lemma(v, i - 1);
                }
                to_nat(v[..i-1]) + to_nat( v[i-1..]) * pow2(i-1);
                {
                    to_nat_split_aux_lemma(v, i);
                }
                to_nat(v[..i]) + to_nat(v[i..]) * pow2(i);
            }
        }
    }

    lemma to_nat_split_aux_lemma(v: cbv, i: uint32)
        requires 1 < i < |v|;
        requires |v| > 1;
        ensures to_nat(v[..i-1]) + to_nat( v[i-1..]) * pow2(i-1) == to_nat(v[..i]) + to_nat(v[i..]) * pow2(i);
    {
        var v1 := v[..i-1];
        var v2 := v[i-1..];
        var v3 := v[i..];
        var v4 := v[..i];

        calc == {
            to_nat(v1) + to_nat(v2) * pow2(i-1);
            {
                assert to_nat(v2) == v[i-1] + to_nat(v3) * 2 by 
                {
                    to_nat_lsb_lemma(v2);
                }
            }
            to_nat(v1) + (v[i-1] + to_nat(v3) * 2) * pow2(i-1);
            to_nat(v1) + v[i-1] * pow2(i-1) + to_nat(v3) * 2 * pow2(i-1);
            {
                assert 2 * pow2(i-1) == pow2(i) by {
                    reveal power();
                }
            }
            to_nat(v1) + v[i-1] * pow2(i-1) + to_nat(v3) * pow2(i);
            {
                assert to_nat(v4) == to_nat(v1) + v[i-1] * pow2(i-1) 
                     by {
                        to_nat_msb_lemma(v4, i);
                        assume v4[..i-1] == v[..i-1];
                    }
            }
            to_nat(v4) + to_nat(v3) * pow2(i);
        }

        assert to_nat(v1) + to_nat(v2) * pow2(i-1) == to_nat(v4) + to_nat(v3) * pow2(i);
        assert to_nat(v[..i-1]) + to_nat( v[i-1..]) * pow2(i-1) == to_nat(v[..i]) + to_nat(v[i..]) * pow2(i);
    }

    // method zero(l: uint32) returns (v: cbv)
    //     ensures |v| == l != 0;
    //     ensures to_nat(v) == 0; 
    // {
    //     var a := new uint32[l];
    //     var i := 0;
    //     while i < l
    //         decreases l - i;
    //         invariant i <= l;
    //         invariant forall j :: 0 <= j < i ==> a[j] == 0;
    //     {
    //         a[i] := 0;
    //         i := i + 1;
    //     }
    //     v := a[..];
    //     assert forall j :: 0 <= j < l ==> v[j] == 0;
    //     zero_lemma(v);
    // }

    function method cbv_zero(l: uint32) : (v: cbv)
        requires l != 0;
        decreases l;
        ensures |v| == l;
    {
        if l == 1 then [0]
        else cbv_zero(l - 1) + [0]
    }

    lemma {:induction l} zero_lemma(v: cbv, l: uint32)
        requires l != 0;
        requires v == cbv_zero(l);
        ensures to_nat(v) == 0;
    {
        if l == 1 {
           calc == {
                to_nat(v);
                to_nat_aux(v, 0) + pow2(0) * v[0];
                0;
            }
        } else {
            calc == {
                to_nat(v);
                {
                    to_nat_msb_lemma(v, l);
                }
                to_nat(v[..l-1]) + pow2(l-1) * msb(v);
                {
                    zero_lemma(cbv_zero(l - 1), l-1);
                }
                0;
            }
        }
    }

    function method cbv_lsr(v: cbv, amt: uint32) : cbv
        requires amt < |v|;
    {
        v[amt..]
    }

    lemma {:induction amt} cbv_lsr_is_div_lemma(v: cbv, v1: cbv, amt: uint32)
        decreases amt;
        requires amt < |v|;
        requires v1 == cbv_lsr(v, amt);
        ensures to_nat(v1) == to_nat(v) / pow2(amt);
    {
        if amt == 0 {
            reveal power();
        } else {
            var v2 := v[amt-1..];

            calc ==> {
                true;
                {
                    cbv_lsr_is_div_lemma(v, v2, amt-1);
                }
                to_nat(v2) == to_nat(v) / pow2(amt-1);
                {
                    assert to_nat(v2) == v2[0] + 2 * to_nat(v2[1..]) by {
                        to_nat_lsb_lemma(v2);
                    }
                }
                to_nat(v) / pow2(amt-1) == v2[0] + 2 * to_nat(v2[1..]);
                {
                    assert to_nat(v1) == to_nat(v2[1..]);
                }
                to_nat(v) / pow2(amt-1) == v2[0] + 2 * to_nat(v1);
                to_nat(v) / pow2(amt-1) / 2 == to_nat(v1);
                {
                    assume to_nat(v) / pow2(amt-1) / 2 == to_nat(v) / (pow2(amt-1) * 2); 
                }
                to_nat(v) / (pow2(amt-1) * 2) == to_nat(v1);
                {
                    assert pow2(amt-1) * 2 == pow2(amt) by {
                        reveal power();
                    }
                }
                to_nat(v) / pow2(amt) == to_nat(v1);
            }

            assert to_nat(v) / pow2(amt) == to_nat(v1);
        }
    }

    function method cbv_sl(v: cbv, amt: uint32) : cbv
    {
        if amt == 0 then v
        else var z := cbv_zero(amt);
        z + v 
    }

    // lemma lshift_is_mul_lemma(v: cbv, v1: cbv, amt: uint32)
    //     decreases amt;
    //     requires amt < |v|;
    //     requires v1 == lshift(v, amt);
    //     ensures to_nat(v1) == to_nat(v) * pow2(amt);
    // {
    //     if amt == 0 {
    //         reveal power();
    //     } else {
    //         var v2 := lshift(v, amt-1);
    //         assume v2 == [0] + v1;
    //         lshift_is_mul_lemma(v, v2, amt-1);
    //         assert to_nat(v2) == to_nat(v) * pow2(amt-1);

    //         assume false;
    //     }
    // }

    // lemma {:axiom} nested_div_lemma(x: nat, m: nat, n: nat) 
    //     requires m != 0 && n != 0;
    //     ensures x / m / n == x / (m * n);

    method cbv_concat(v1: cbv, v2: cbv) returns (v3: cbv)
    {
        return v1 + v2; 
    }

    method cbv_slice(v: cbv, lo: uint32, hi: uint32) returns (v': cbv)
        requires 0 <= lo < hi <= |v|;
        ensures v' == v[lo..hi];
    {
        v' := v[lo..hi];
    }

    method cbv_zext(v: cbv, l': uint32) returns (v': cbv)
        requires l' > |v|;
        ensures |v'| == l';
        ensures to_nat(v') == to_nat(v);
    {
        var l := |v|;
        var z := cbv_zero(l' - l);
        v' := v + z;

        calc == {
            to_nat(v');
            {
                to_nat_split_lemma(v', l);
            }
            to_nat(v'[..l]) + to_nat(v'[l..]) * pow2(l);
            {
                assert z == v'[l..];
            }
            to_nat(v'[..l]) + to_nat(z) * pow2(l);
            {
                assert z == cbv_zero(l' - l);
                zero_lemma(z , l' - l);
            }
            to_nat(v'[..l]);
            to_nat(v);
        }
        assert to_nat(v') == to_nat(v);
    }

    // method cbv_add(v1: cbv, v2: cbv) returns (v3: cbv)
    //     // ensures |v3| == |v1| + 1;
    //     ensures to_nat(v3) == to_nat(v1) + to_nat(v2);
}