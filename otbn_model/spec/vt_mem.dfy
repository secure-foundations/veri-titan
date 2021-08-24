include "vt_consts.dfy"
include "bv_ops.dfy"

module vt_mem {
    import opened bv_ops
    import opened vt_consts

    import opened NativeTypes

    type xmem_t = map<int, uint32>

    predicate method xmem_addr_admissible(addr: uint32)
    {
        && addr % 4 == 0
        && addr < DMEM_LIMIT
    }    

    predicate xmem_addr_valid(xmem: xmem_t, addr: uint32)
    {
        && xmem_addr_admissible(addr)
        && addr in xmem
    }

    predicate xmem_addr_mapped(xmem: xmem_t, addr: uint32, value: uint32)
    {
        && xmem_addr_valid(xmem, addr)
        && xmem[addr] == value
    }

/*  wmem_t definion */

    type wmem_t = map<nat, uint256>

    function method wmem_offsetted_addr(base: uint32, offset: int10): uint32
    {
        uint32_addi(base, offset * 32)
    }

    // admissible is aligned and bounded
    predicate method wmem_addr_admissible(addr: nat)
    {
        && addr % 32 == 0
        && addr < DMEM_LIMIT
    }

    // valid address is admissible and mapped
    predicate wmem_addr_valid(wmem: wmem_t, addr: nat)
    {
        && wmem_addr_admissible(addr)
        && addr in wmem
    }

/* heap_t definion (SHADOW) */

    type heap_t = map<nat, seq<uint256>>

    function heap_indexed_addr(addr: nat, i: nat): nat
    {
        addr + 32 * i
    }

    predicate heap_base_addr_valid(heap: heap_t, addr: int)
    {
        && addr in heap
        // buff is not empty
        && |heap[addr]| != 0
        // address is also admissible
        && wmem_addr_admissible(heap_indexed_addr(addr, |heap[addr]|))
    }

/* iter_t definion (SHADOW) */

    datatype iter_t = iter_cons(base_addr: nat, index: nat, buff: seq<uint256>)

    predicate iter_inv(iter: iter_t, heap: heap_t, address: nat)
    {
        var base_addr := iter.base_addr;
        // base_addr points to a valid buffer
        && heap_base_addr_valid(heap, base_addr)
        // address is correct
        && address == heap_indexed_addr(base_addr, iter.index)
        // the view is consistent with heap
        && heap[base_addr] == iter.buff
        // the index is within bound (or at end)
        && iter.index <= |iter.buff|
    }

    predicate iter_safe(iter: iter_t, heap: heap_t, address: nat)
    {
        && iter_inv(iter, heap, address)
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

/* heap_t/wmem_t correspondence */

    // this holds for a given buffer in heap_t
    predicate heap_buff_inv(heap: heap_t, wmem: wmem_t, base_addr: nat)
        requires base_addr in heap
    {
        var buff := heap[base_addr];
        var len := |buff|;
        && heap_base_addr_valid(heap, base_addr)
        && (forall i | 0 <= i < len ::
            (var sub_addr := heap_indexed_addr(base_addr, i);
            && wmem_addr_valid(wmem, sub_addr)
            && wmem[sub_addr] == buff[i]))
        && (forall i | 0 < i < len ::
            heap_indexed_addr(base_addr, i) !in heap)
    }

    // this holds for a given cell in wmem_t
    predicate wmem_cell_inv(heap: heap_t, wmem: wmem_t, addr: nat)
        requires addr in wmem
    {
        exists iter :: iter_safe(iter, heap, addr)
    }

    function get_iter(wmem: wmem_t, addr: nat, heap: heap_t) : iter_t
        requires addr in wmem
        requires wmem_cell_inv(heap, wmem, addr)
    {
        var iter :| iter_safe(iter, heap, addr);
        iter
    }

    predicate mem_equiv(heap: heap_t, wmem: wmem_t)
    {
        && (forall base_addr | base_addr in heap ::
            heap_buff_inv(heap, wmem, base_addr))
        && (forall addr | addr in wmem ::
            wmem_cell_inv(heap, wmem, addr))
    }

/* correspondence lemmas */

    // lemma read_equiv(wmem: wmem_t, addr: nat, heap: heap_t, iter: iter_t)
    //     requires wmem_addr_valid(wmem, addr)
    //     requires mem_equiv(heap, wmem)
    //     requires iter_safe(iter, heap, addr)
    //     ensures wmem[addr] == iter.buff[iter.index]
    // {
    // }

    // given an address, there is an unique iter to it
    lemma addess_iter_unique(wmem: wmem_t, addr: nat, heap: heap_t)
        requires wmem_addr_valid(wmem, addr)
        requires mem_equiv(heap, wmem)
        ensures forall alt_iter | iter_safe(alt_iter, heap, addr) 
            :: alt_iter == get_iter(wmem, addr, heap);
    {
        var iter := get_iter(wmem, addr, heap);

        forall alt_iter | iter_safe(alt_iter, heap, addr)
            ensures iter == alt_iter;
        {
            var base, i := iter.base_addr, iter.index;
            var alt_base, j := alt_iter.base_addr, alt_iter.index;
            assert base + 32 * i == alt_base + 32 * j;

            if alt_base != base {
                if alt_base > base {
                    var buff, len := heap[base], |heap[base]|;
                    assert heap_buff_inv(heap, wmem, base);
                    var k := i - j;
                    assert 0 < k < len;
                    assert alt_base == heap_indexed_addr(base, k);
                    assert alt_base !in heap;
                } else {
                    var buff, len := heap[alt_base], |heap[alt_base]|;
                    assert heap_buff_inv(heap, wmem, alt_base);
                    var k := j - i;
                    assert 0 < k < len;
                    assert base == heap_indexed_addr(alt_base, k);
                    assert base !in heap;
                }
                assert false; 
            }
            assert alt_base == base && i == j;
        }
    }

    lemma sub_address_rooted(wmem: wmem_t, base: nat, i: nat, heap: heap_t)
        requires mem_equiv(heap, wmem)
        requires heap_base_addr_valid(heap, base)
        requires 0 <= i < |heap[base]|
        ensures get_iter(wmem, heap_indexed_addr(base, i), heap) == iter_cons(base, i, heap[base])
    {
        assert heap_buff_inv(heap, wmem, base);

        var buff := heap[base]; 
        var sub_addr := heap_indexed_addr(base, i);
        assert sub_addr in wmem;
        assert wmem[sub_addr] == buff[i];

        var iter := iter_cons(base, i, heap[base]);
        assert iter_safe(iter, heap, sub_addr);
        addess_iter_unique(wmem, sub_addr, heap);
    }

    function write_heap(addr: nat, value: uint256, heap: heap_t, iter: iter_t): (heap_t, iter_t)
        requires iter_safe(iter, heap, addr)
        ensures var (heap', iter') := write_heap(addr, value, heap, iter);
            iter_safe(iter', heap', addr)
    {
        var buff := heap[iter.base_addr];
        var new_buff := buff[iter.index := value];
        (heap[iter.base_addr := new_buff], iter.(buff := new_buff))
    }

    lemma write_preverses_heap_inv(
        wmem: wmem_t, write_addr: nat, value: uint256,
        base_addr: nat,
        heap: heap_t, iter: iter_t,
        heap': heap_t, iter': iter_t)

        requires wmem_addr_valid(wmem, write_addr)
        requires mem_equiv(heap, wmem)
        requires iter_safe(iter, heap, write_addr)
        requires write_heap(write_addr, value, heap, iter) == (heap', iter')

        requires base_addr in heap'

        ensures heap_buff_inv(heap', wmem[write_addr := value], base_addr)
    {
        var wmem' := wmem[write_addr := value];
        addess_iter_unique(wmem, write_addr, heap);
        var base, j := iter.base_addr, iter.index;

        var buff := heap[base_addr];
        var len := |buff|;

        assert heap_base_addr_valid(heap', base_addr);
        assert forall i | 0 < i < len :: heap_indexed_addr(base_addr, i) !in heap';

        assert heap_buff_inv(heap, wmem, base_addr);

        if base_addr != base {
            assert heap'[base_addr] == buff;

            forall i | 0 <= i < len
                ensures var sub_addr := heap_indexed_addr(base_addr, i);
                    && wmem_addr_valid(wmem', sub_addr)
                    && wmem'[sub_addr] == buff[i]
            {
                var sub_addr := heap_indexed_addr(base_addr, i);
                if sub_addr == write_addr {
                    sub_address_rooted(wmem, base_addr, i, heap);
                    assert false;
                }
            }
        } else {
            var buff' := iter'.buff;
            assert heap'[base_addr] == buff'[j := value];

            forall i | 0 <= i < len
                ensures var sub_addr := heap_indexed_addr(base_addr, i);
                    && wmem_addr_valid(wmem', sub_addr)
                    && wmem'[sub_addr] == buff'[i]
            {
                var sub_addr := heap_indexed_addr(base_addr, i);
                if i == j {
                    assert sub_addr == write_addr;
                    assert wmem'[sub_addr] == value; 
                }
            }
        }
    }

    lemma write_equiv(wmem: wmem_t, write_addr: nat, value: uint256, heap: heap_t, iter: iter_t)
        requires wmem_addr_valid(wmem, write_addr)
        requires mem_equiv(heap, wmem)
        requires iter_safe(iter, heap, write_addr)

        ensures
            var wmem' := wmem[write_addr := value];
            var (heap', iter') := write_heap(write_addr, value, heap, iter);
            && mem_equiv(heap', wmem')
            && iter_safe(iter', heap', write_addr)
    {
        var wmem' := wmem[write_addr := value];
        var (heap', iter') := write_heap(write_addr, value, heap, iter);
        
        forall base_addr | base_addr in heap'
            ensures heap_buff_inv(heap', wmem', base_addr)
        {
            write_preverses_heap_inv(wmem, write_addr, value,
                base_addr, heap, iter, heap', iter');
        }

        forall addr | addr in wmem'
            ensures wmem_cell_inv(heap', wmem', addr)
        {
            var iter := get_iter(wmem, addr, heap);
            if iter.base_addr != iter'.base_addr {
                assert iter_safe(iter, heap', addr);
            } else {
                assert addr == heap_indexed_addr(iter.base_addr, iter.index);
                assert iter'.base_addr == iter.base_addr;
                var iter'' := iter'.(index := iter.index);
                assert iter_safe(iter'', heap', addr);
            }
        }
    }
}
