include "vt_consts.dfy"
include "bv_ops.dfy"

module vt_mem {
    import opened bv_ops
    import opened vt_consts
    import opened NativeTypes

/* mem_t definion */

    // admissible is aligned and bounded
    predicate method xword_ptr_admissible(ptr: nat)
    {
        && ptr % 4 == 0
        && ptr < DMEM_LIMIT
    }

    // admissible is aligned and bounded
    predicate method wword_ptr_admissible(ptr: nat)
    {
        && ptr % 32 == 0
        && ptr < DMEM_LIMIT
    }

    type mem_t = map<int, uint32>

    predicate wword_ptr_valid(mem: mem_t, ptr: nat)
    {
        && wword_ptr_admissible(ptr)
        && ptr + 0 in mem
        && ptr + 4 in mem
        && ptr + 8 in mem
        && ptr + 12 in mem
        && ptr + 16 in mem
        && ptr + 20 in mem
        && ptr + 24 in mem
        && ptr + 28 in mem
    }

    function method read_wword(mem: mem_t, ptr: nat): uint256
        requires wword_ptr_valid(mem, ptr)
    {
        // reveal wword_ptr_valid();
        var p0 := mem[ptr + 0];
        var p1 := mem[ptr + 4];
        var p2 := mem[ptr + 8];
        var p3 := mem[ptr + 12];
        var p4 := mem[ptr + 16];
        var p5 := mem[ptr + 20];
        var p6 := mem[ptr + 24];
        var p7 := mem[ptr + 28];
        uint256_eighth_assemble(p0, p1, p2, p3, p4, p5, p6, p7)
    }

    function method wirte_wword(mem: mem_t, ptr: nat, value: uint256): (mem' : mem_t)
        requires wword_ptr_admissible(ptr)
        ensures wword_ptr_valid(mem', ptr)
    {
        mem[ptr + 0 := uint256_eighth_split(value, 0)]
            [ptr + 4 := uint256_eighth_split(value, 1)]
            [ptr + 8 := uint256_eighth_split(value, 2)]
            [ptr + 12 := uint256_eighth_split(value, 3)]
            [ptr + 16 := uint256_eighth_split(value, 4)]
            [ptr + 20 := uint256_eighth_split(value, 5)]
            [ptr + 24 := uint256_eighth_split(value, 6)]
            [ptr + 28 := uint256_eighth_split(value, 7)]
    }

    lemma uint256_eighth_value(v: uint256)
        ensures v == uint256_eighth_assemble(
            uint256_eighth_split(v, 0),
            uint256_eighth_split(v, 1),
            uint256_eighth_split(v, 2),
            uint256_eighth_split(v, 3),
            uint256_eighth_split(v, 4),
            uint256_eighth_split(v, 5),
            uint256_eighth_split(v, 6),
            uint256_eighth_split(v, 7))
    {
        assume false;
    }

    // lemma mem_wword_consistency(
    //     mem: mem_t, mem': mem_t,
    //     ptr: nat, value: uint256,
    //     other_ptr: nat)
    //     requires wword_ptr_admissible(ptr)
    //     requires mem' == wirte_wword(mem, ptr, value)
    //     ensures read_wword(mem', ptr) == value
    // {
    //     uint256_eighth_value(value);
    // }

/* heap_t definion (SHADOW) */

    datatype entry_t = 
        | XWORD(v: uint32)
        | WBUFF(b: seq<uint256>)

    type heap_t = map<int, entry_t>

    function buff_indexed_ptr(ptr: nat, i: nat): nat
    {
        ptr + 32 * i
    }

    predicate is_buff_base_ptr(heap: heap_t, ptr: nat)
    {
        // ptr is mapped
        && ptr in heap
        // ptr maps to a buffer
        && heap[ptr].WBUFF?
    }

    predicate is_xword_ptr(heap: heap_t, ptr: nat)
    {
        && ptr in heap
        // ptr maps to a buffer
        && heap[ptr].XWORD?
    }

    // a valid base pointer that points to the beginning of a buffer
    predicate buff_base_ptr_valid(heap: heap_t, ptr: nat)
        requires is_buff_base_ptr(heap, ptr)
    {
        var len := |heap[ptr].b|;
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

        && is_buff_base_ptr(heap, base_ptr)
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
        requires is_buff_base_ptr(heap, base_ptr)
    {
        && buff_base_ptr_valid(heap, base_ptr)
        && var buff := heap[base_ptr].b;
        && var len := |buff|;
        // map each uint256
        && (forall i | 0 <= i < len ::
            wword_inv(heap, mem, base_ptr, i, buff[i]))
    }

    predicate heap_xword_inv(heap: heap_t, mem: mem_t, ptr: nat)
        requires is_xword_ptr(heap, ptr)
    {
        && xword_ptr_admissible(ptr)
        && ptr in heap
        && ptr in mem
        && heap[ptr].v == mem[ptr]
    }

    // this holds for a given cell in wmem_t
    // predicate wmem_cell_inv(heap: heap_t, wmem: wmem_t, ptr: nat)
    //     requires ptr in wmem
    // {
    //     exists iter :: iter_safe(iter, heap, ptr)
    // }

    // function get_iter(wmem: wmem_t, ptr: nat, heap: heap_t) : iter_t
    //     requires ptr in wmem
    //     requires wmem_cell_inv(heap, wmem, ptr)
    // {
    //     var iter :| iter_safe(iter, heap, ptr);
    //     iter
    // }

    predicate mem_equiv(heap: heap_t, mem: mem_t)
    {
        && (forall base_ptr | is_buff_base_ptr(heap, base_ptr) ::
            heap_wbuff_inv(heap, mem, base_ptr))
        && (forall base_ptr | is_xword_ptr(heap, base_ptr) ::
            heap_xword_inv(heap, mem, base_ptr))
        // && (forall ptr | ptr in mem ::
        //     wmem_cell_inv(heap, mem, ptr))
    }

/* correspondence lemmas */

    lemma read_equiv(heap: heap_t, iter: iter_t, mem: mem_t, ptr: nat)
        requires wword_ptr_valid(mem, ptr)
        requires mem_equiv(heap, mem)
        requires iter_safe(iter, heap, ptr)
        ensures iter.buff[iter.index] == read_wword(mem, ptr)
    {
    }

    function heap_write_wword(heap: heap_t, iter: iter_t, ptr: nat, value: uint256): (heap_t, iter_t)
        requires iter_safe(iter, heap, ptr)
        ensures var (heap', iter') := heap_write_wword(heap, iter, ptr, value);
            iter_safe(iter', heap', ptr)
    {
        var buff := heap[iter.base_ptr].b;
        var new_buff := buff[iter.index := value];
        (heap[iter.base_ptr := WBUFF(new_buff)], iter.(buff := new_buff))
    }

    lemma sub_ptrs_disjoint(heap: heap_t, mem: mem_t, base1: nat, base2: nat)
        requires mem_equiv(heap, mem)
        requires is_buff_base_ptr(heap, base1)
        requires is_buff_base_ptr(heap, base2)
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
        iter: iter_t, iter': iter_t,
        mem: mem_t, mem': mem_t,
        write_ptr: nat, value: uint256,
        other_ptr: nat)

        requires mem_equiv(heap, mem)
        requires iter_safe(iter, heap, write_ptr)
        requires is_buff_base_ptr(heap, other_ptr)
        requires heap_wbuff_inv(heap, mem, other_ptr)
        requires (heap', iter') == heap_write_wword(heap, iter, write_ptr, value)

        ensures is_buff_base_ptr(heap', other_ptr)
        ensures heap_wbuff_inv(heap', mem', other_ptr)
    {
        var mem' := wirte_wword(mem, write_ptr, value);

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
                    uint256_eighth_value(value);
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

//     lemma write_equiv(wmem: wmem_t, write_ptr: nat, value: uint256, heap: heap_t, iter: iter_t)
//         requires buff_base_ptr_valid(wmem, write_ptr)
//         requires mem_equiv(heap, wmem)
//         requires iter_safe(iter, heap, write_ptr)

//         ensures
//             var wmem' := wmem[write_ptr := value];
//             var (heap', iter') := write_heap(write_ptr, value, heap, iter);
//             && mem_equiv(heap', wmem')
//             && iter_safe(iter', heap', write_ptr)
//     {
//         var wmem' := wmem[write_ptr := value];
//         var (heap', iter') := write_heap(write_ptr, value, heap, iter);
        
//         forall base_ptr | base_ptr in heap'
//             ensures heap_wbuff_inv(heap', wmem', base_ptr)
//         {
//             write_preverses_heap_inv(wmem, write_ptr, value,
//                 base_ptr, heap, iter, heap', iter');
//         }

//         forall ptr | ptr in wmem'
//             ensures wmem_cell_inv(heap', wmem', ptr)
//         {
//             var iter := get_iter(wmem, ptr, heap);
//             if iter.base_ptr != iter'.base_ptr {
//                 assert iter_safe(iter, heap', ptr);
//             } else {
//                 assert ptr == buff_indexed_ptr(iter.base_ptr, iter.index);
//                 assert iter'.base_ptr == iter.base_ptr;
//                 var iter'' := iter'.(index := iter.index);
//                 assert iter_safe(iter'', heap', ptr);
//             }
//         }
//     }
}
