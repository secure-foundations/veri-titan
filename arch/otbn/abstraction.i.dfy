include "machine.s.dfy"

module ot_abstraction {
    import opened integers
    import opened bv256_ops
    import opened ot_machine

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
        var result := bv256_ops.ls(x, num_bits);
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

/* heap_t definion (SHADOW) */

    datatype entry_t = 
        | XWORD(v: uint32)
        | WBUFF(b: seq<uint256>)

    type heap_t = map<int, entry_t>

    function buff_indexed_ptr(ptr: nat, i: nat): nat
    {
        ptr + 32 * i
    }

    predicate xword_ptr_valid(heap: heap_t, ptr: nat)
    {
        && xword_ptr_admissible(ptr)
        // ptr is mapped
        && ptr in heap
        // ptr maps to a word
        && heap[ptr].XWORD?
    }

    predicate is_xword_pointee(heap: heap_t, ptr: nat, value: uint32)
    {
        && xword_ptr_valid(heap, ptr)
        && heap[ptr].v == value
    }

    // a valid base pointer that points to the beginning of a buffer
    predicate buff_base_ptr_valid(heap: heap_t, ptr: nat)
    {
        // ptr is mapped
        && ptr in heap
        // ptr maps to a buffer
        && heap[ptr].WBUFF?

        && var len := |heap[ptr].b|;
        // buff is not empty
        && len != 0
        // end of the buffer does not extend beyond mem limit
        && wword_ptr_admissible(buff_indexed_ptr(ptr, len))
    }

/* iter_t definion (SHADOW) */

    datatype iter_t = iter_cons(base_ptr: nat, index: nat, buff: seq<uint256>)

    predicate iter_inv(iter: iter_t, heap: heap_t, ptress: nat)
    {
        var base_ptr := iter.base_ptr;

        // base_ptr points to a valid buffer
        && buff_base_ptr_valid(heap, base_ptr)
        // ptress is correct
        && ptress == buff_indexed_ptr(base_ptr, iter.index)
        // the view is consistent with heap
        && heap[base_ptr].b == iter.buff
        // the index is within bound (or at end)
        && iter.index <= |iter.buff|
    }

    predicate iter_safe(iter: iter_t, heap: heap_t, ptress: nat)
    {
        && iter_inv(iter, heap, ptress)
        // tighter constraint so we can dereference
        && iter.index < |iter.buff|
    }

    function bn_lid_next_iter(iter: iter_t, inc: bool): iter_t
    {
        iter.(index := if inc then iter.index + 1 else iter.index)
    }

    function bn_sid_next_iter(iter: iter_t, value: uint256, inc: bool): iter_t
        requires iter.index < |iter.buff|
    {
        iter.(index := if inc then iter.index + 1 else iter.index)
            .(buff := iter.buff[iter.index := value])
    }

/* mem_t/heap_t correspondence */
    predicate wword_inv(heap: heap_t, mem: mem_t,
        base_ptr: nat, i: nat, value: uint256)
    {
        var ptr := buff_indexed_ptr(base_ptr, i);
        && wword_ptr_valid(mem, ptr)
        && read_wword(mem, ptr) == value

        && (i != 0 ==> ptr !in heap)
        && ptr + 4 !in heap
        && ptr + 8 !in heap
        && ptr + 12 !in heap
        && ptr + 16 !in heap
        && ptr + 20 !in heap
        && ptr + 24 !in heap
        && ptr + 28 !in heap
    }

    // this holds for a given buffer in heap_t
    predicate heap_wbuff_inv(heap: heap_t, mem: mem_t, base_ptr: nat)
    {
        && buff_base_ptr_valid(heap, base_ptr)
        && var buff := heap[base_ptr].b;
        && var len := |buff|;
        // map each uint256
        && (forall i | 0 <= i < len ::
            wword_inv(heap, mem, base_ptr, i, buff[i]))
    }

    predicate heap_xword_inv(heap: heap_t, mem: mem_t, ptr: nat)
        requires xword_ptr_valid(heap, ptr)
    {
        && xword_ptr_admissible(ptr)
        && ptr in heap
        && ptr in mem
        && heap[ptr].v == mem[ptr]
    }

    predicate mem_equiv(heap: heap_t, mem: mem_t)
    {
        && (forall base_ptr | buff_base_ptr_valid(heap, base_ptr) ::
            heap_wbuff_inv(heap, mem, base_ptr))
        && (forall base_ptr | xword_ptr_valid(heap, base_ptr) ::
            heap_xword_inv(heap, mem, base_ptr))
    }

/* correspondence lemmas */

    lemma read_equiv(heap: heap_t, iter: iter_t, mem: mem_t, ptr: nat)
        requires wword_ptr_valid(mem, ptr)
        requires mem_equiv(heap, mem)
        requires iter_safe(iter, heap, ptr)
        ensures iter.buff[iter.index] == read_wword(mem, ptr)
    {
    }

    // these boiler plates are needed 
    function heap_read_xword(heap: heap_t, ptr: nat): uint32
        requires xword_ptr_valid(heap, ptr)
    {
        heap[ptr].v
    }

    function heap_write_xword(heap: heap_t, ptr: nat, value: uint32): heap_t
        requires xword_ptr_valid(heap, ptr)
    {
        heap[ptr := XWORD(value)]
    }

    function heap_write_wword(heap: heap_t, iter: iter_t, ptr: nat, value: uint256): heap_t
        requires iter_safe(iter, heap, ptr)
    {
        var buff := heap[iter.base_ptr].b;
        var new_buff := buff[iter.index := value];
        heap[iter.base_ptr := WBUFF(new_buff)]
    }

    lemma sub_ptrs_disjoint(heap: heap_t, mem: mem_t, base1: nat, base2: nat)
        requires mem_equiv(heap, mem)
        requires buff_base_ptr_valid(heap, base1)
        requires buff_base_ptr_valid(heap, base2)
        requires base1 != base2
        ensures forall i, j ::
            (0 <= i < |heap[base1].b| && 0 <= j < |heap[base2].b|)
                ==> 
            (buff_indexed_ptr(base1, i) != buff_indexed_ptr(base2, j))
    {
        if exists i, j ::
            && 0 <= i < |heap[base1].b|
            && 0 <= j < |heap[base2].b|
            && buff_indexed_ptr(base1, i) == buff_indexed_ptr(base2, j)
        {
            var i, j :|
                && 0 <= i < |heap[base1].b|
                && 0 <= j < |heap[base2].b|
                && buff_indexed_ptr(base1, i) == buff_indexed_ptr(base2, j);
            assert base1 + 32 * i == base2 + 32 * j;
            var buff1 := heap[base1].b;
            var buff2 := heap[base2].b;

            if base1 > base2 {
                assert heap_wbuff_inv(heap, mem, base2);
                var k := j - i;
                assert base1 == buff_indexed_ptr(base2, k);
                assert 0 <= k < |buff2|;
                assert wword_inv(heap, mem, base2, k, buff2[k]);
                assert base1 !in heap;
                assert false;
            } else {
                assert heap_wbuff_inv(heap, mem, base1);
                var k := i - j;
                assert base2 == buff_indexed_ptr(base1, k);
                assert 0 <= k < |buff1|;
                assert wword_inv(heap, mem, base1, k, buff1[k]);
                assert base2 !in heap;
                assert false;
            }
        }
    }

    lemma write_wword_preverses_heap_wbuff_inv(
        heap: heap_t, heap': heap_t,
        iter: iter_t, 
        mem: mem_t, mem': mem_t,
        write_ptr: nat, value: uint256,
        other_ptr: nat)

        requires mem_equiv(heap, mem)
        requires iter_safe(iter, heap, write_ptr)
        requires buff_base_ptr_valid(heap, other_ptr)
        requires heap_wbuff_inv(heap, mem, other_ptr)
        requires heap' == heap_write_wword(heap, iter, write_ptr, value)
        requires mem' == mem_write_wword(mem, write_ptr, value)

        ensures buff_base_ptr_valid(heap', other_ptr)
        ensures heap_wbuff_inv(heap', mem', other_ptr)
    {
        var base_ptr, j := iter.base_ptr, iter.index;
        var buff := heap[other_ptr].b;
        var buff' := heap'[other_ptr].b;
        var len := |buff|;

        if other_ptr == base_ptr {
            forall i | 0 <= i < len
                ensures wword_inv(heap', mem', base_ptr, i, buff'[i])
            {
                assert wword_inv(heap, mem, base_ptr, i, buff[i]);
                if i == j {
                    eighth_value(value);
                    assert wword_inv(heap', mem', base_ptr, i, value);
                }
            }
        } else {
            forall i | 0 <= i < len
                ensures wword_inv(heap', mem', other_ptr, i, buff'[i])
            {
                assert wword_inv(heap, mem, other_ptr, i, buff[i]);
                var ptr := buff_indexed_ptr(other_ptr, i);
                assert wword_ptr_valid(mem', ptr);
                assert ptr != write_ptr by {
                    sub_ptrs_disjoint(heap, mem, other_ptr, base_ptr);
                }
                assert read_wword(mem', ptr) == buff[i];
            }
        }
        assert heap_wbuff_inv(heap', mem', other_ptr);
    }

    lemma write_wword_preverses_heap_xword_inv(
        heap: heap_t, heap': heap_t,
        iter: iter_t, 
        mem: mem_t, mem': mem_t,
        write_ptr: nat, value: uint256,
        other_ptr: nat)

        requires mem_equiv(heap, mem)
        requires iter_safe(iter, heap, write_ptr)
        requires xword_ptr_valid(heap, other_ptr)
        requires heap_xword_inv(heap, mem, other_ptr)
        requires heap' == heap_write_wword(heap, iter, write_ptr, value)
        requires mem' == mem_write_wword(mem, write_ptr, value)

        ensures xword_ptr_valid(heap', other_ptr)
        ensures heap_xword_inv(heap', mem', other_ptr)
    {
        assert heap[other_ptr] == heap'[other_ptr];

        if mem[other_ptr] != mem'[other_ptr] {
            var i :| && i % 4 == 0
                && 0 <= i <= 28
                && write_ptr + i == other_ptr;
            assert wword_inv(heap, mem, iter.base_ptr, iter.index, iter.buff[iter.index]);
            assert false;
        }
    }

    lemma write_wword_preverses_mem_equiv(
        heap: heap_t, heap': heap_t,
        iter: iter_t,
        mem: mem_t, mem': mem_t,
        write_ptr: nat, value: uint256)

        requires mem_equiv(heap, mem)
        requires iter_safe(iter, heap, write_ptr)

        requires heap' == heap_write_wword(heap, iter, write_ptr, value)
        requires mem' == mem_write_wword(mem, write_ptr, value)
    
        ensures mem_equiv(heap', mem')
    {
        forall base_ptr | buff_base_ptr_valid(heap', base_ptr)
            ensures heap_wbuff_inv(heap', mem', base_ptr)
        {
            write_wword_preverses_heap_wbuff_inv(heap, heap',
                iter, mem, mem', write_ptr, value, base_ptr);
        }
        forall base_ptr | xword_ptr_valid(heap', base_ptr)
            ensures heap_xword_inv(heap', mem', base_ptr)
        {
            write_wword_preverses_heap_xword_inv(heap, heap',
                iter, mem, mem', write_ptr, value, base_ptr);
        }
    }

    lemma write_xword_preverses_mem_equiv(
        heap: heap_t, heap': heap_t,
        mem: mem_t, mem': mem_t,
        write_ptr: nat, value: uint32)
        requires mem_equiv(heap, mem)
        requires xword_ptr_valid(heap, write_ptr)

        requires heap' == heap_write_xword(heap, write_ptr, value)
        requires mem' == mem[write_ptr := value]

        ensures mem_equiv(heap', mem')
    {
        forall base_ptr | buff_base_ptr_valid(heap', base_ptr)
            ensures heap_wbuff_inv(heap', mem', base_ptr)
        {
            assert heap_wbuff_inv(heap, mem, base_ptr);
        }
        forall base_ptr | xword_ptr_valid(heap', base_ptr)
            ensures heap_xword_inv(heap', mem', base_ptr)
        {
            assert heap_xword_inv(heap, mem, base_ptr);
        }
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
        requires xword_ptr_admissible(addr + words * 4)
    {
        var end := addr + words * 4;
        var cur := addr;
        var i := 0;

        while cur < end
            invariant cur == addr + i * 4
            invariant xword_ptr_admissible(cur)
            decreases end - cur
        {
            var value := s.read_xword(cur);
            print(cur); print(":"); print_as_hex(value, 4); print("\n");
            cur := cur + 4;
            i := i + 1;
        }
    }
}