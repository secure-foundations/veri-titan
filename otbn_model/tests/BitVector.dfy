include "NativeTypes.dfy"
include "../lib/powers.dfy"

module CutomBitVector {
    import opened NativeTypes
    import opened powers

    // lsb .. msb
    type cbv = t: seq<uint1> | 0 < |t| <= UINT32_MAX witness [1]

    type cbv384 = t: cbv | |t| == 384

    type cbv385 = t: cbv | |t| == 385

    type cbv768 = t: cbv | |t| == 768

    function {:opaque} to_nat(v: cbv) : nat
    {
        to_nat_aux(v, |v|)
    }

    // function {:fuel 20} to_nat_aux(v: cbv, i: uint32) : nat
    function to_nat_aux(v: cbv, i: uint32) : nat
        decreases i;
        requires 0 <= i <= |v|;
    {
        if i == 0 then 0
        else to_nat_aux(v, i - 1) + pow2(i - 1) * v[i - 1]
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
                assume false;
                // assert to_nat(v3) * 2 * pow2(i-1) == to_nat(v3) * pow2(i) by {
                //     reveal power();
                // }
            }
            to_nat(v1) + v[i-1] * pow2(i-1) + to_nat(v3) * pow2(i);
            {
                assert to_nat(v4) == to_nat(v1) + v[i-1] * pow2(i-1) by {
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

    function method zero(l: uint32) : (v: cbv)
        requires l != 0;
        decreases l;
        ensures |v| == l;
    {
        if l == 1 then [0]
        else zero(l - 1) + [0]
    }

    lemma {:induction l} zero_lemma(v: cbv, l: uint32)
        requires l != 0;
        requires v == zero(l);
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
                    zero_lemma(zero(l - 1), l-1);
                }
                0;
            }
        }
    }

    function method rshift(v: cbv, amt: uint32) : cbv
        requires amt < |v|;
    {
        v[amt..]
    }

    lemma {:induction amt} rshift_is_div_lemma(v: cbv, v1: cbv, amt: uint32)
        decreases amt;
        requires amt < |v|;
        requires v1 == rshift(v, amt);
        ensures to_nat(v1) == to_nat(v) / pow2(amt);
    {
        if amt == 0 {
            reveal power();
        } else {
            var v2 := v[amt-1..];

            calc ==> {
                true;
                {
                    rshift_is_div_lemma(v, v2, amt-1);
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

    function method lshift(v: cbv, amt: uint32) : cbv
    {
        if amt == 0 then v
        else var z := zero(amt);
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

    function method concat(v1: cbv, v2: cbv) : (v3: cbv)
    {
        v1 + v2
    }

    method slice(v: cbv, lo: uint32, hi: uint32) returns (v': cbv)
        requires 0 <= lo < hi <= |v|;
        ensures v' == v[lo..hi];
    {
        v' := v[lo..hi];
    }

    method bvzero_extend(v: cbv, l': uint32) returns (v': cbv)
        requires l' > |v|;
        ensures |v'| == l';
        ensures to_nat(v') == to_nat(v);
    {
        var l := |v|;
        var z := zero(l' - l);
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
                assert z == zero(l' - l);
                zero_lemma(z , l' - l);
            }
            to_nat(v'[..l]);
            to_nat(v);
        }
        assert to_nat(v') == to_nat(v);
    }

    function method {:opaque} add(v1: cbv, v2: cbv, cin: uint1) : (cbv, uint1)
        requires |v1| == |v2|;
        ensures
            var (v3, c) := add(v1, v2, cin);
            var sum := to_nat(v1) + to_nat(v2) + cin;
        |v3| == |v1| && to_nat(v3) == sum % pow2(|v1|) && c == sum / pow2(|v1|);
    {
        assume false;
        (add_aux(v1, v2, 0), 0)
    }

    function method add_aux(v1: cbv, v2: cbv, c: uint1) : (v3: cbv)
        requires |v1| == |v2|;
    {
        if |v1| == 0 then []
        else 
        var b1 := v1[0];
        var b2 := v2[0];
        var s : int := b1 as int + b2 as int;
        [s % 2] + add_aux(v1[1..], v2[1..], s / 2)
    }

    predicate equal_uint256(bv: cbv, v: uint256)
    {
        |bv| == 256 && to_nat(bv) == v
    }

    predicate equal_uint512(bv: cbv, v1: uint256, v2: uint256)
    {
        |bv| == 512 && to_nat(bv) == v1 + v2 * BASE_256
    }

    // predicate equal_uint256_seq(bv: cbv, vs: seq<uint256>)
    // {
    //     (|bv| == 256 * vs) && to_nat(bv) == 
    // }

    method cbv_test()
    {
        // var a: cbv := [1, 1, 1, 0, 1];

        // assert to_nat(a) == 23 by {
        //     reveal power();
        // }

        // a := slice(a, 1, 5);
        // assert a == [1, 1, 0, 1];
        // assert to_nat(a) == 11 by {
        //     reveal power();
        // }

        // a := rshift(a, 2);
        // assert a == [0, 1];
    }
}