include "../../std_lib/src/Collections/Sequences/LittleEndianNat.dfy"

abstract module dw_add refines LittleEndianNat {
    // import opened Mul
    // import opened Power
    // import opened DivMod

    function DWBASE(): nat
    {
        Mul.LemmaMulStrictlyPositive(BASE(), BASE());
        BASE() * BASE()
    }

    // type uint_dw = i: int | 0 <= i < DWBASE()
    //     witness *

    type uint1   = i :int | 0 <= i < 2

    function method uint_addc(x: uint, y: uint, cin: uint1): (uint, uint1)
    {
        var sum : int := x + y + cin;
        var sum_out := if sum < BASE() then sum else sum - BASE();
        var cout := if sum  < BASE() then 0 else 1;
        (sum_out, cout)
    }

    function method uint_add(x: uint, y: uint): uint
    {
        uint_addc(x, y, 0).0
    }

    predicate uint_dw_add_is_safe(
        x_lh: uint, x_uh: uint,
        y_lh: uint, y_uh: uint)
    {
        ToNatRight([x_lh, x_uh]) + ToNatRight([y_lh, y_uh]) < DWBASE()
    }

    lemma uint_dw_add_correct(
        x_lh: uint, x_uh: uint,
        y_lh: uint, y_uh: uint,
        c1: uint1, c2: uint1,
        z_lh: uint, z_uh: uint)

        requires uint_dw_add_is_safe(x_lh, x_uh, y_lh, y_uh);
        requires (z_lh, c1) == uint_addc(x_lh, y_lh, 0);
        requires (z_uh, c2) == uint_addc(x_uh, y_uh, c1);
        
        ensures ToNatRight([z_lh, z_uh]) == ToNatRight([x_lh, x_uh]) + ToNatRight([y_lh, y_uh]);
    {
        var x_full := ToNatRight([x_lh, x_uh]);
        var y_full := ToNatRight([y_lh, y_uh]);
        var z_full := ToNatRight([z_lh, z_uh]);

        assert SeqAdd([x_lh], [y_lh]) == ([z_lh], c1) by {
            reveal SeqAdd();
            assert [] + [z_lh] == [z_lh];
        }

        assert SeqAdd([x_lh, x_uh], [y_lh, y_uh]) == ([z_lh, z_uh], c2) by {
            reveal SeqAdd();
            assert [z_lh] + [z_uh] == [z_lh, z_uh];
        }

        assert ToNatRight([z_lh, z_uh]) + c2 * Pow(BASE(), 2) == x_full + ToNatRight([y_lh, y_uh]) by {
            LemmaSeqAdd([x_lh, x_uh], [y_lh, y_uh], [z_lh, z_uh], c2);
        }

        if c2 != 0 {
            reveal Pow();
            assert false;
        }
    }

    method dw_add(x_lh: uint, x_uh: uint, y_lh: uint, y_uh: uint)
        requires uint_dw_add_is_safe(x_lh, x_uh, y_lh, y_uh);
    {
        var (z_lh, c1) := uint_addc(x_lh, y_lh, 0);
        var (z_uh, c2) := uint_addc(x_uh, y_uh, c1);
        uint_dw_add_correct(x_lh, x_uh, y_lh, y_uh, c1, c2, z_lh, z_uh);
    }
    
    // function method full_mul(a: uint, b: uint): (lh: uint, uh: uint)
    // {
    //     var full := a * b;
    //     ()
    // }

    // method mul_add(a: uint, b: uint， c: uint)
    // {
        

    // }
}