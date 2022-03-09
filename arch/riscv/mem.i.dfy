include "stack.i.dfy"

module mem {
  import opened integers
  import opened flat
  import opened stack

  datatype entry_t = 
    | W32(w32: uint32)
    | B32(b32: seq<uint32>)

  type heap_t = map<int, entry_t>

  function heap_b32_index_ptr(ptr: nat, i: nat): nat
  {
    ptr + 4 * i
  }

  predicate heap_b32_ptr_valid(heap: heap_t, base_ptr: nat)
  {
    && ptr_admissible_32(base_ptr)
    && base_ptr in heap
    && heap[base_ptr].B32?
    && var len := |heap[base_ptr].b32|;
    //  the buffer is not empty
    && len != 0
    // end of buffer is in bound
    && ptr_admissible_32(heap_b32_index_ptr(base_ptr, len - 1))
  }

  // this holds for each uint32 in a b32 heaplet entry
  predicate heap_32_inv(heap: heap_t, flat: flat_t, base_ptr: nat, i: nat)
    requires heap_b32_ptr_valid(heap, base_ptr)
    requires i < |heap[base_ptr].b32|
  {
    var ptr := heap_b32_index_ptr(base_ptr, i);
    // ptr points to some uint32, which has 8 base words uint32
    && flat_ptr_valid_32(flat, ptr)
    && flat_read_32(flat, ptr) == heap[base_ptr].b32[i]
    // disjointness
    && (i != 0 ==> ptr !in heap)
    && !in_stack_addr_range(ptr + 0)
    && ptr + 0 !in heap
  }

  // this holds for each b32 heaplet entry
  predicate heap_b32_inv(heap: heap_t, flat: flat_t, base_ptr: nat)
    requires heap_b32_ptr_valid(heap, base_ptr)
  {
    forall i | 0 <= i < |heap[base_ptr].b32| ::
      heap_32_inv(heap, flat, base_ptr, i)
  }

  function heap_b32_read(heap: heap_t, iter: b32_iter): uint32
    requires b32_iter_safe(heap, iter)
  {
    var buff := heap[iter.base_ptr].b32;
    buff[iter.index]
  }

  function heap_b32_write(heap: heap_t, iter: b32_iter, value: uint32): heap_t
    requires b32_iter_safe(heap, iter)
  {
    var buff := heap[iter.base_ptr].b32;
    var new_buff := buff[iter.index := value];
    heap[iter.base_ptr := B32(new_buff)]
  }


  // iterator for buffer entries
  datatype b32_iter = b32_iter_cons(base_ptr: nat, index: nat, buff: seq<uint32>)
  {
    function cur_ptr(): nat {
      heap_b32_index_ptr(base_ptr, index)
    }
  }

  function b32_iter_load_next(iter: b32_iter, inc: bool): b32_iter
  {
    iter.(index := if inc then iter.index + 1 else iter.index)
  }

  function b32_iter_store_next(iter: b32_iter, value: uint32, inc: bool): b32_iter
    requires iter.index < |iter.buff|
  {
      iter.(index := if inc then iter.index + 1 else iter.index)
          .(buff := iter.buff[iter.index := value])
  }

  predicate b32_iter_inv(heap: heap_t, iter: b32_iter)
  {
    var base_ptr := iter.base_ptr;
    // base_ptr points to a valid buffer
    && heap_b32_ptr_valid(heap, base_ptr)
    // ptr is correct
    && iter.cur_ptr() == heap_b32_index_ptr(base_ptr, iter.index)
    // the view is consistent with heap
    && heap[base_ptr].b32 == iter.buff
    // the index is within bound (or at end)
    && iter.index <= |iter.buff|
  }

  predicate b32_iter_safe(heap: heap_t, iter: b32_iter)
  {
    && b32_iter_inv(heap, iter)
    // tighter constraint so we can dereference
    && iter.index < |iter.buff|
  }

  // valid pointer for W32 heaplet entry
  predicate heap_w32_ptr_valid(heap: heap_t, base_ptr: nat)
  {
    && ptr_admissible_32(base_ptr)
    && base_ptr in heap
    && heap[base_ptr].W32?
  }

  function heap_w32_read(heap: heap_t, ptr: nat): uint32
    requires heap_w32_ptr_valid(heap, ptr)
  {
    heap[ptr].w32
  }

  function heap_w32_write(heap: heap_t, ptr: nat, value: uint32): heap_t
    requires heap_w32_ptr_valid(heap, ptr)
  {
    heap[ptr := W32(value)]
  }

  // this holds for each W32 heaplet entry
  predicate heap_w32_inv(heap: heap_t, flat: flat_t, ptr: nat)
    requires heap_w32_ptr_valid(heap, ptr)
  {
    && flat_ptr_valid_32(flat, ptr)
    && heap[ptr].w32 == flat_read_32(flat, ptr)
    // disjointness from stack
    && !in_stack_addr_range(ptr)
  }

  predicate stack_addrs_valid(flat: flat_t)
  {
    forall i | 0 <= i < STACK_MAX_WORDS() ::
      flat_ptr_valid_32(flat, stack_index_to_ptr(i))
  }

  function {:opaque} get_stack(flat: flat_t): (stack: seq<uint32>)
    requires stack_addrs_valid(flat)
    ensures |stack| ==  STACK_MAX_WORDS()
  {
    seq(STACK_MAX_WORDS(),
      n requires 0 <= n < STACK_MAX_WORDS() =>
        flat_read_32(flat, stack_index_to_ptr(n)))
  }

  datatype imem_t = imem_cons(heap: heap_t, stack: seq<uint32>)
  {
    predicate stack_inv(flat: flat_t)
    {
      && stack_addrs_valid(flat)
      && stack == get_stack(flat)
      && (forall i | 0 <= i < STACK_MAX_WORDS() ::
        stack_index_to_ptr(i) !in heap)
    }

    // the equivalence invariant between heaplet and memory
    predicate inv(flat: flat_t)
    {
      && (forall base_ptr | heap_b32_ptr_valid(heap, base_ptr) ::
        heap_b32_inv(heap, flat, base_ptr))
      && (forall base_ptr | heap_w32_ptr_valid(heap, base_ptr) ::
        heap_w32_inv(heap, flat, base_ptr))
      && stack_inv(flat)
    }

    function stack_write(i: nat, value: uint32): imem_t
      requires i < |stack|
    {
      this.(stack := stack[i:= value])
    }

    lemma sub_ptrs_disjoint(flat: flat_t, base1: nat, base2: nat)
      requires inv(flat)
      requires heap_b32_ptr_valid(heap, base1)
      requires heap_b32_ptr_valid(heap, base2)
      requires base1 != base2
      ensures forall i, j ::
        (0 <= i < |heap[base1].b32| && 0 <= j < |heap[base2].b32|)
          ==> 
        (heap_b32_index_ptr(base1, i) != heap_b32_index_ptr(base2, j))
    {
      var heap := heap;
      if exists i, j ::
        && 0 <= i < |heap[base1].b32|
        && 0 <= j < |heap[base2].b32|
        && heap_b32_index_ptr(base1, i) == heap_b32_index_ptr(base2, j)
      {
        var i, j :|
          && 0 <= i < |heap[base1].b32|
          && 0 <= j < |heap[base2].b32|
          && heap_b32_index_ptr(base1, i) == heap_b32_index_ptr(base2, j);
        assert base1 + 4 * i == base2 + 4 * j;
        var buff1 := heap[base1].b32;
        var buff2 := heap[base2].b32;

        if base1 > base2 {
          assert heap_b32_inv(heap, flat, base2);
          var k := j - i;
          assert base1 == heap_b32_index_ptr(base2, k);
          assert 0 <= k < |buff2|;
          assert heap_32_inv(heap, flat, base2, k);
          assert base1 !in heap;
          assert false;
        } else {
          assert heap_b32_inv(heap, flat, base1);
          var k := i - j;
          assert base2 == heap_b32_index_ptr(base1, k);
          assert 0 <= k < |buff1|;
          assert heap_32_inv(heap, flat, base1, k);
          assert base2 !in heap;
          assert false;
        }
      }
    }

    lemma heap_b32_write_preserves_b32_inv(
      flat: flat_t, new_flat: flat_t,
      iter: b32_iter, value: uint32,
      other_ptr: nat)

      requires inv(flat)
      requires b32_iter_safe(heap, iter)
      requires new_flat == flat_write_32(flat, iter.cur_ptr(), value)
      requires heap_b32_ptr_valid(heap, other_ptr)

      ensures heap_b32_inv(heap_b32_write(heap, iter, value),
        flat_write_32(flat, iter.cur_ptr(), value), other_ptr)
    {
      var new_heap := heap_b32_write(heap, iter, value);
      var base_ptr, j := iter.base_ptr, iter.index;
      var buff := heap[other_ptr].b32;
      var len := |buff|;

      if other_ptr == base_ptr {
        forall i | 0 <= i < len
          ensures heap_32_inv(new_heap, new_flat, base_ptr, i)
        {
          assert heap_32_inv(heap, flat, base_ptr, i);
          if i == j {
            value_32_from_32(value);
            assert heap_32_inv(new_heap, new_flat, base_ptr, i);
          }
        }
      } else {
        forall i | 0 <= i < len
          ensures heap_32_inv(new_heap, new_flat, other_ptr, i)
        {
          assert heap_32_inv(heap, flat, other_ptr, i);
          var ptr := heap_b32_index_ptr(other_ptr, i);
          assert flat_ptr_valid_32(new_flat, ptr);
          assert ptr != iter.cur_ptr() by {
            sub_ptrs_disjoint(flat, other_ptr, base_ptr);
          }
          assert flat_read_32(new_flat, ptr) == buff[i];
        }
      }
      assert heap_b32_inv(heap, flat, other_ptr);
    }

    lemma heap_b32_write_preserves_stack_inv(
      flat: flat_t, new_flat: flat_t,
      iter: b32_iter, value: uint32)

      requires inv(flat)
      requires b32_iter_safe(heap, iter)
      requires new_flat == flat_write_32(flat, iter.cur_ptr(), value)

      ensures this.(heap := heap_b32_write(heap, iter, value)).stack_inv(new_flat)
    {
      var new_heap := heap_b32_write(heap, iter, value);
      var new_mem := this.(heap := new_heap);
  
      assert (this.(heap := new_heap)).stack_inv(new_flat) by {
        forall n | 0 <= n < STACK_MAX_WORDS()
          ensures flat_read_32(flat, stack_index_to_ptr(n))
            == 
          flat_read_32(new_flat, stack_index_to_ptr(n))
        {
          var ptr := stack_index_to_ptr(n);
          if flat[ptr] != new_flat[ptr] {
            assert heap_32_inv(heap, flat, iter.base_ptr, iter.index);
            assert false;
          }
        }
        reveal get_stack();
      }
    }

    lemma heap_b32_write_preserves_w32_inv(
      flat: flat_t, new_flat: flat_t,
      iter: b32_iter, value: uint32, other_ptr: nat)

      requires inv(flat)
      requires b32_iter_safe(heap, iter)
      requires new_flat == flat_write_32(flat, iter.cur_ptr(), value)
      requires heap_w32_ptr_valid(heap, other_ptr)

      ensures heap_w32_inv(heap_b32_write(heap, iter, value), new_flat, other_ptr)
    {
      if flat[other_ptr] != new_flat[other_ptr] {
        assert heap_32_inv(heap, flat, iter.base_ptr, iter.index);
        assert false;
      }
    }
  
    lemma heap_b32_write_preverses_inv(
      flat: flat_t, new_flat: flat_t,
      iter: b32_iter, value: uint32)

      requires inv(flat)
      requires b32_iter_safe(heap, iter)
      requires new_flat == flat_write_32(flat, iter.cur_ptr(), value)

      ensures this.(heap := heap_b32_write(heap, iter, value)).inv(new_flat)
    {
      var new_heap := heap_b32_write(heap, iter, value);
      var new_mem := this.(heap := new_heap);

      forall base_ptr | heap_b32_ptr_valid(new_heap, base_ptr)
        ensures heap_b32_inv(new_heap, new_flat, base_ptr)
      {
        heap_b32_write_preserves_b32_inv(flat, new_flat, iter, value, base_ptr);
      }
      forall base_ptr | heap_w32_ptr_valid(new_heap, base_ptr)
        ensures heap_w32_inv(new_heap, new_flat, base_ptr)
      {
        heap_b32_write_preserves_w32_inv(flat, new_flat, iter, value, base_ptr);
      }

      heap_b32_write_preserves_stack_inv(
        flat, new_flat, iter, value);
    }

    lemma heap_w32_write_preserves_b32_inv(
      flat: flat_t, new_flat: flat_t,
      write_ptr: nat, value: uint32, other_ptr: nat)

      requires inv(flat)
      requires heap_w32_ptr_valid(heap, write_ptr)
      requires new_flat == flat_write_32(flat, write_ptr, value)

      requires heap_b32_ptr_valid(heap, other_ptr)

      ensures heap_b32_inv(heap_w32_write(heap, write_ptr, value), new_flat, other_ptr)
    {
      var new_heap := heap_w32_write(heap, write_ptr, value);
      assert heap_b32_inv(heap, flat, other_ptr);
      var buff := heap[other_ptr].b32;
      forall i | 0 <= i < |buff| 
        ensures heap_32_inv(new_heap, new_flat, other_ptr, i)
      {
        assert heap_32_inv(heap, flat, other_ptr, i);
      }
    }

    lemma heap_w32_write_preserves_w32_inv(
      flat: flat_t, new_flat: flat_t,
      write_ptr: nat, value: uint32, other_ptr: nat)

      requires inv(flat)
      requires heap_w32_ptr_valid(heap, write_ptr)
      requires new_flat == flat_write_32(flat, write_ptr, value)

      requires heap_w32_ptr_valid(heap, other_ptr)

      ensures heap_w32_inv(heap_w32_write(heap, write_ptr, value), new_flat, other_ptr)
    {
      if other_ptr == write_ptr {
        value_32_from_32(value);
      }
    }

    lemma heap_w32_write_preserves_stack_inv(
      flat: flat_t, new_flat: flat_t,
      value: uint32, write_ptr: nat)

      requires inv(flat)
      requires heap_w32_ptr_valid(heap, write_ptr)
      requires new_flat == flat_write_32(flat, write_ptr, value)

      ensures this.(heap := heap_w32_write(heap, write_ptr, value)).stack_inv(new_flat)
    {
      var new_heap := heap_w32_write(heap, write_ptr, value);
  
      assert (this.(heap := new_heap)).stack_inv(new_flat) by {
        reveal get_stack();
      }
    }

    lemma heap_w32_write_preverses_inv(
      flat: flat_t, new_flat: flat_t,
      write_ptr: nat, value: uint32)

      requires inv(flat)
      requires heap_w32_ptr_valid(heap, write_ptr)
      requires new_flat == flat_write_32(flat, write_ptr, value)

      ensures this.(heap := heap_w32_write(heap, write_ptr, value)).inv(new_flat)
    {
      var new_heap := heap_w32_write(heap, write_ptr, value);

      forall base_ptr | heap_b32_ptr_valid(new_heap, base_ptr)
        ensures heap_b32_inv(new_heap, new_flat, base_ptr)
      {
        heap_w32_write_preserves_b32_inv(flat, new_flat, write_ptr, value, base_ptr);
      }
      forall base_ptr | heap_w32_ptr_valid(new_heap, base_ptr)
        ensures heap_w32_inv(new_heap, new_flat, base_ptr)
      {
        heap_w32_write_preserves_w32_inv(flat, new_flat, write_ptr, value, base_ptr);
      }
      heap_w32_write_preserves_stack_inv(flat, new_flat, value, write_ptr);
    }

    lemma stack_write_preserves_b32_inv(
      flat: flat_t, new_flat: flat_t,
      index: nat, value: uint32, base_ptr: nat)

      requires inv(flat)
      requires index < |stack|
      requires new_flat == flat_write_32(flat, stack_index_to_ptr(index), value)
      requires heap_b32_ptr_valid(heap, base_ptr)
  
      ensures heap_b32_inv(heap, new_flat, base_ptr)
    {
      var buff := heap[base_ptr].b32;
      var new_buff := heap[base_ptr].b32;
  
      forall i | 0 <= i < |new_buff|
        ensures heap_32_inv(heap, new_flat, base_ptr, i) 
      {
        assert heap_32_inv(heap, flat, base_ptr, i);
      }
    }

    lemma stack_write_preserves_w32_inv(
      flat: flat_t, new_flat: flat_t,
      index: nat, value: uint32,
      other_ptr: nat)

      requires inv(flat)
      requires index < |stack|
      requires new_flat == flat_write_32(flat, stack_index_to_ptr(index), value)
      requires heap_w32_ptr_valid(heap, other_ptr)

      ensures heap_w32_inv(heap, new_flat, other_ptr)
    {
    }

    lemma stack_write_preserves_stack_inv(
      flat: flat_t, new_flat: flat_t,
      index: nat, value: uint32)

      requires inv(flat)
      requires index < |stack|
      requires new_flat == flat_write_32(flat, stack_index_to_ptr(index), value)
  
      ensures this.(stack := stack[index := value]).stack_inv(new_flat)
    {
      var new_stack := stack[index := value];
      reveal get_stack();
      value_32_from_32(value);
      assert get_stack(new_flat) == new_stack;
    }

    lemma stack_write_preverses_inv(
      flat: flat_t, new_flat: flat_t,
      index: nat, value: uint32)

      requires inv(flat)
      requires index < |stack|
      requires new_flat == flat_write_32(flat, stack_index_to_ptr(index), value)

      ensures this.(stack := stack[index := value]).inv(new_flat)
    {
      forall base_ptr | heap_b32_ptr_valid(heap, base_ptr)
        ensures heap_b32_inv(heap, new_flat, base_ptr)
      {
        stack_write_preserves_b32_inv(flat, new_flat, index, value, base_ptr);
      }
      
      forall base_ptr | heap_w32_ptr_valid(heap, base_ptr)
        ensures heap_w32_inv(heap, new_flat, base_ptr)
      {
        stack_write_preserves_w32_inv(flat, new_flat, index, value, base_ptr);
      }
    
      stack_write_preserves_stack_inv(flat, new_flat,
        index, value);
    }
  }

  datatype mem_t = mem_cons(heap: heap_t, frames: frames_t)
  {
    function as_imem(flat: flat_t): imem_t
      requires stack_addrs_valid(flat)
    {
      imem_cons(heap, get_stack(flat))
    }

    predicate {:opaque} inv(flat: flat_t)
    {
      && stack_addrs_valid(flat)
      && as_imem(flat).inv(flat)
      && frames.frames_inv(get_stack(flat))
    }

    lemma heap_b32_write_preverses_inv(
      flat: flat_t, iter: b32_iter, value: uint32)

      requires inv(flat)
      requires b32_iter_safe(heap, iter)

      ensures this.(heap := heap_b32_write(heap, iter, value)).
        inv(flat_write_32(flat, iter.cur_ptr(), value))
    {
      reveal inv();
      var new_flat := flat_write_32(flat, iter.cur_ptr(), value);
      as_imem(flat).heap_b32_write_preverses_inv(flat, new_flat,
        iter, value);
    }

    lemma heap_w32_write_preverses_inv(
      flat: flat_t, write_ptr: nat, value: uint32)
    
      requires inv(flat)
      requires heap_w32_ptr_valid(heap, write_ptr)
      ensures this.(heap := heap_w32_write(heap, write_ptr, value)).
        inv(flat_write_32(flat, write_ptr, value))
    {
      reveal inv();
      var new_flat := flat_write_32(flat, write_ptr, value);
      as_imem(flat).heap_w32_write_preverses_inv(flat, new_flat,
        write_ptr, value);
    }

    lemma frames_write_preverses_inv(flat: flat_t, index: nat, value: uint32)
      requires inv(flat)
      requires frames.write.requires(index, value)

      ensures in_stack_addr_range(frames.sp + index * 4)
      ensures this.(frames := frames.write(index, value)).
        inv(flat_write_32(flat, frames.sp + index * 4, value))
    {
      reveal inv();

      var new_mem := this.(frames := frames.write(index, value));
      var stack_index := ptr_to_stack_index(frames.sp) + index;
      var write_ptr := stack_index_to_ptr(stack_index);

      calc == {
        write_ptr;
        STACK_END() + (ptr_to_stack_index(frames.sp) + index) * 4;
        {
          Mul.LemmaMulIsDistributiveAddAuto();
        }
        STACK_END() + ptr_to_stack_index(frames.sp) * 4 + index * 4;
        STACK_END() + ((frames.sp - STACK_END()) / 4) * 4 + index * 4;
        {
          assert DivMod.IsModEquivalent(frames.sp, STACK_END(), 4);  // pain
          LemmaDivMulNop(frames.sp - STACK_END(), 4); 
        }
        frames.sp + index * 4;
      }

      var new_flat := flat_write_32(flat, frames.sp + index * 4, value);
      var stack := get_stack(flat);

      frames.write_preserves_inv(stack, index, value);

      assert new_mem.frames.
        frames_inv(stack[stack_index := value]);

      as_imem(flat).stack_write_preverses_inv(flat, new_flat,
        stack_index, value);

      assert as_imem(flat).(stack := stack[stack_index := value]).inv(new_flat);
    }
  }

  function push_frame(mem: mem_t, flat: flat_t, num_bytes: uint32): (new_mem: mem_t)
    requires mem.inv(flat)
    requires num_bytes % 4 == 0
    requires in_stack_addr_range(mem.frames.sp - num_bytes)
    ensures new_mem.inv(flat)
  {
    reveal mem.inv();
    var stack := get_stack(flat);
    mem.frames.push_preserves_inv(num_bytes, get_stack(flat));
    var new_mem := mem.(frames := mem.frames.push(num_bytes, stack));
    assert new_mem.inv(flat);
    new_mem
  }

  function write_frame(mem: mem_t, flat: flat_t, index: nat, value: uint32): (r: (mem_t, flat_t))
    requires mem.inv(flat)
    requires frames_writable(mem.frames, index)
    ensures in_stack_addr_range(mem.frames.sp + index * 4)
    ensures r.1 == flat_write_32(flat, mem.frames.sp + index * 4, value)
    ensures r.0.inv(r.1)
  {
    mem.frames_write_preverses_inv(flat, index, value);
    var new_mem := mem.(frames := mem.frames.write(index, value));
    var new_flat := flat_write_32(flat, mem.frames.sp + index * 4, value);
    (new_mem, new_flat)
  }

  function read_frame(mem: mem_t, flat: flat_t, index: nat): (value: uint32)
    requires mem.inv(flat)
    requires frames_writable(mem.frames, index)
    // ensures value == flat_read_32(flat, mem.frames.sp + index * 4)
  {
    mem.frames.read(index)
  }
}