include "machine.s.dfy"

module ot_abstraction {
    import opened integers
    import opened bv256_op_s
    import opened ot_machine
    import opened flat

/* safe stateless operations */

    // quater shift but no overflow

    predicate otbn_qshift_is_safe(x: uint256, q: uint2)
    {
        && (q == 1 ==> x < BASE_192)
        && (q == 2 ==> x < BASE_128)
        && (q == 3 ==> x < BASE_64)
    }

    function otbn_qshift_safe(x: uint256, q: uint2): (r: uint256)
        requires otbn_qshift_is_safe(x, q);
    {
        if q == 0 then x
        else if q == 1 then x * BASE_64
        else if q == 2 then x * BASE_128
        else x * BASE_192
    }

    lemma otbn_qshift_safe_correct_lemma(x: uint256, q: uint2)
        requires otbn_qshift_is_safe(x, q);
        ensures otbn_qshift_safe(x, q) == otbn_shift(x, SFT(true, q * 8));
    {
        var num_bytes := q * 8;
        assert 0 <= num_bytes <= 24;
        var shift := SFT(true, num_bytes);
        var num_bits := num_bytes * 8;
        var result := bv256_op_s.ls(x, num_bits);
        ls_is_mul(x, num_bytes, result);
        assert otbn_qshift_safe(x, q) == otbn_shift(x, shift);
    }

    predicate otbn_mulqacc_is_safe(shift: uint2, acc: uint256)
    {
        // make sure no overflow from shift (product needs to be 128 bits)
        && (shift <= 2) 
        // make sure no overflow from addtion
        && (acc + otbn_qshift_safe(BASE_128 - 1, shift) < BASE_256)
    }

    // mulqacc but no overflow
    function otbn_mulqacc_safe(
        zero: bool,
        x: uint256, qx: uint2,
        y: uint256, qy: uint2,
        shift: uint2,
        acc: uint256) : uint256

        requires otbn_mulqacc_is_safe(shift, acc);
    {
        var product := otbn_qmul(x, qx, y, qy);
        var shift := otbn_qshift_safe(product, shift);
        if zero then shift else acc + shift
    }

    lemma otbn_mulqacc_safe_correct_lemma(
        zero: bool,
        x: uint256, qx: uint2,
        y: uint256, qy: uint2,
        shift: uint2,
        acc: uint256)
        requires otbn_mulqacc_is_safe(shift, acc);
        ensures otbn_mulqacc_safe(zero, x, qx, y, qy, shift, acc)
            == otbn_mulqacc(zero, x, qx, y, qy, shift, acc);
    {
        var product := otbn_qmul(x, qx, y, qy);
        otbn_qshift_safe_correct_lemma(product, shift);
    }

/* wdr_view definion (SHADOW) */

    predicate valid_wdr_view(wdrs: wdrs_t, view: seq<uint256>, start: nat, len: nat)
    {   
        && |view| == len
        && start + len <= 32
        && wdrs[start..start+len] == view
    }

/* debug prints */

    method print_as_hex(a: nat, bytes: nat)
    {
        var val := a;
        var num_digits := bytes * 2;
        var i := 0;
        var result := "";
        while i < num_digits
            decreases num_digits - i
        {
            var digit := val % 16;
            if digit == 0 {
                result := "0" + result;
            } else if digit == 1 {
                result := "1" + result;
            } else if digit == 2 {
                result := "2" + result;
            } else if digit == 3 {
                result := "3" + result;
            } else if digit == 4 {
                result := "4" + result;
            } else if digit == 5 {
                result := "5" + result;
            } else if digit == 6 {
                result := "6" + result;
            } else if digit == 7 {
                result := "7" + result;
            } else if digit == 8 {
                result := "8" + result;
            } else if digit == 9 {
                result := "9" + result;
            } else if digit == 10 {
                result := "a" + result;
            } else if digit == 11 {
                result := "b" + result;
            } else if digit == 12 {
                result := "c" + result;
            } else if digit == 13 {
                result := "d" + result;
            } else if digit == 14 {
                result := "e" + result;
            } else if digit == 15 {
                result := "f" + result;
            }
            val := val / 16;
            i := i + 1;
        }
        print("0x"); print(result);
    }

    method dump_regs(s: state)
    {
        var i := 0;
        while i < 32
        {
            print(" x"); print(i); 
            if i < 10 {
                print("  = ");
            } else {
                print(" = ");
            }
            print_as_hex(s.read_reg32(GPR(i)), 4); print("\n"); 
            i := i + 1;
        }

        i := 0;
        while i < 32
        {
            print(" w"); print(i);
            if i < 10 {
                print("  = ");
            } else {
                print(" = ");
            }
            print_as_hex(s.read_reg256(WDR(i)), 32); print("\n"); 
            i := i + 1;
        }

        print(" fg0 = ");print_as_hex(flags_as_uint(s.fgroups.fg0), 4); print("\n"); 
        print(" fg1 = ");print_as_hex(flags_as_uint(s.fgroups.fg1), 4); print("\n"); 
    }

    method dump_mem(s: state, addr: uint32, words: uint32)
        requires ptr_admissible_32(addr + words * 4)
    {
        var end := addr + words * 4;
        var cur := addr;
        var i := 0;

        while cur < end
            invariant cur == addr + i * 4
            invariant ptr_admissible_32(cur)
            decreases end - cur
        {
            var value := s.read_xword(cur);
            print(cur); print(":"); print_as_hex(value, 4); print("\n");
            cur := cur + 4;
            i := i + 1;
        }
    }
}