include "stack.i.dfy"

module mem {
  import opened integers
  import opened flat
  import opened stack

  datatype entry_t = 
    | W32(w32: uint32)
    | B256(b256: seq<uint256>)

  type heap_t = map<int, entry_t>

  function heap_b256_index_ptr(ptr: nat, i: nat): nat
  {
    ptr + 32 * i
  }

  predicate heap_b256_ptr_valid(heap: heap_t, base_ptr: nat)
  {
    && ptr_admissible_256(base_ptr)
    && base_ptr in heap
    && heap[base_ptr].B256?
    && var len := |heap[base_ptr].b256|;
    //  the buffer is not empty
    && len != 0
    // end of buffer is in bound
    && ptr_admissible_256(heap_b256_index_ptr(base_ptr, len - 1))
  }

  // this holds for each uint256 in a b256 heaplet entry
  predicate heap_256_inv(heap: heap_t, flat: flat_t, base_ptr: nat, i: nat)
    requires heap_b256_ptr_valid(heap, base_ptr)
    requires i < |heap[base_ptr].b256|
  {
    var ptr := heap_b256_index_ptr(base_ptr, i);
    // ptr points to some uint256, which has 8 base words uint32
    && flat_ptr_valid_256(flat, ptr)
    && flat_read_256(flat, ptr) == heap[base_ptr].b256[i]
    // disjointness
    && (i != 0 ==> ptr !in heap)
    && ptr + 4 !in heap
    && ptr + 8 !in heap
    && ptr + 12 !in heap
    && ptr + 16 !in heap
    && ptr + 20 !in heap
    && ptr + 24 !in heap
    && ptr + 28 !in heap
    && !in_stack_addr_range(ptr + 0)
    && ptr + 0 !in heap
    && !in_stack_addr_range(ptr + 4)
    && ptr + 4 !in heap
    && !in_stack_addr_range(ptr + 8)
    && ptr + 8 !in heap
    && !in_stack_addr_range(ptr + 12)
    && ptr + 12 !in heap
    && !in_stack_addr_range(ptr + 16)
    && ptr + 16 !in heap
    && !in_stack_addr_range(ptr + 20)
    && ptr + 20 !in heap
    && !in_stack_addr_range(ptr + 24)
    && ptr + 24 !in heap
    && !in_stack_addr_range(ptr + 28)
    && ptr + 28 !in heap
  }

  // this holds for each b256 heaplet entry
  predicate heap_b256_inv(heap: heap_t, flat: flat_t, base_ptr: nat)
    requires heap_b256_ptr_valid(heap, base_ptr)
  {
    forall i | 0 <= i < |heap[base_ptr].b256| ::
      heap_256_inv(heap, flat, base_ptr, i)
  }

  function heap_b256_read(heap: heap_t, iter: b256_iter): uint256
    requires b256_iter_safe(heap, iter)
  {
    var buff := heap[iter.base_ptr].b256;
    buff[iter.index]
  }

  function heap_b256_write(heap: heap_t, iter: b256_iter, value: uint256): heap_t
    requires b256_iter_safe(heap, iter)
  {
    var buff := heap[iter.base_ptr].b256;
    var new_buff := buff[iter.index := value];
    heap[iter.base_ptr := B256(new_buff)]
  }


  // iterator for buffer entries
  datatype b256_iter = b256_iter_cons(base_ptr: nat, index: nat, buff: seq<uint256>)
  {
    function cur_ptr(): nat {
      heap_b256_index_ptr(base_ptr, index)
    }
  }

  function b256_iter_load_next(iter: b256_iter, inc: bool): b256_iter
  {
    iter.(index := if inc then iter.index + 1 else iter.index)
  }

  function b256_iter_store_next(iter: b256_iter, value: uint256, inc: bool): b256_iter
    requires iter.index < |iter.buff|
  {
      iter.(index := if inc then iter.index + 1 else iter.index)
          .(buff := iter.buff[iter.index := value])
  }

  predicate b256_iter_inv(heap: heap_t, iter: b256_iter)
  {
    var base_ptr := iter.base_ptr;
    // base_ptr points to a valid buffer
    && heap_b256_ptr_valid(heap, base_ptr)
    // the view is consistent with heap
    && heap[base_ptr].b256 == iter.buff
    // the index is within bound (or at end)
    && iter.index <= |iter.buff|
  }

  predicate b256_iter_safe(heap: heap_t, iter: b256_iter)
  {
    && b256_iter_inv(heap, iter)
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
      && (forall base_ptr | heap_b256_ptr_valid(heap, base_ptr) ::
        heap_b256_inv(heap, flat, base_ptr))
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
      requires heap_b256_ptr_valid(heap, base1)
      requires heap_b256_ptr_valid(heap, base2)
      requires base1 != base2
      ensures forall i, j ::
        (0 <= i < |heap[base1].b256| && 0 <= j < |heap[base2].b256|)
          ==> 
        (heap_b256_index_ptr(base1, i) != heap_b256_index_ptr(base2, j))
    {
      var heap := heap;
      if exists i, j ::
        && 0 <= i < |heap[base1].b256|
        && 0 <= j < |heap[base2].b256|
        && heap_b256_index_ptr(base1, i) == heap_b256_index_ptr(base2, j)
      {
        var i, j :|
          && 0 <= i < |heap[base1].b256|
          && 0 <= j < |heap[base2].b256|
          && heap_b256_index_ptr(base1, i) == heap_b256_index_ptr(base2, j);
        assert base1 + 32 * i == base2 + 32 * j;
        var buff1 := heap[base1].b256;
        var buff2 := heap[base2].b256;

        if base1 > base2 {
          assert heap_b256_inv(heap, flat, base2);
          var k := j - i;
          assert base1 == heap_b256_index_ptr(base2, k);
          assert 0 <= k < |buff2|;
          assert heap_256_inv(heap, flat, base2, k);
          assert base1 !in heap;
          assert false;
        } else {
          assert heap_b256_inv(heap, flat, base1);
          var k := i - j;
          assert base2 == heap_b256_index_ptr(base1, k);
          assert 0 <= k < |buff1|;
          assert heap_256_inv(heap, flat, base1, k);
          assert base2 !in heap;
          assert false;
        }
      }
    }

    lemma heap_b256_write_preserves_b256_inv(
      flat: flat_t, new_flat: flat_t,
      iter: b256_iter, value: uint256,
      other_ptr: nat)

      requires inv(flat)
      requires b256_iter_safe(heap, iter)
      requires new_flat == flat_write_256(flat, iter.cur_ptr(), value)
      requires heap_b256_ptr_valid(heap, other_ptr)

      ensures heap_b256_inv(heap_b256_write(heap, iter, value),
        flat_write_256(flat, iter.cur_ptr(), value), other_ptr)
    {
      var new_heap := heap_b256_write(heap, iter, value);
      var base_ptr, j := iter.base_ptr, iter.index;
      var buff := heap[other_ptr].b256;
      var len := |buff|;

      if other_ptr == base_ptr {
        forall i | 0 <= i < len
          ensures heap_256_inv(new_heap, new_flat, base_ptr, i)
        {
          assert heap_256_inv(heap, flat, base_ptr, i);
          if i == j {
            value_256_from_32(value);
            assert heap_256_inv(new_heap, new_flat, base_ptr, i);
          }
        }
      } else {
        forall i | 0 <= i < len
          ensures heap_256_inv(new_heap, new_flat, other_ptr, i)
        {
          assert heap_256_inv(heap, flat, other_ptr, i);
          var ptr := heap_b256_index_ptr(other_ptr, i);
          assert flat_ptr_valid_256(new_flat, ptr);
          assert ptr != iter.cur_ptr() by {
            sub_ptrs_disjoint(flat, other_ptr, base_ptr);
          }
          assert flat_read_256(new_flat, ptr) == buff[i];
        }
      }
      assert heap_b256_inv(heap, flat, other_ptr);
    }

    lemma heap_b256_write_preserves_stack_inv(
      flat: flat_t, new_flat: flat_t,
      iter: b256_iter, value: uint256)

      requires inv(flat)
      requires b256_iter_safe(heap, iter)
      requires new_flat == flat_write_256(flat, iter.cur_ptr(), value)

      ensures this.(heap := heap_b256_write(heap, iter, value)).stack_inv(new_flat)
    {
      var new_heap := heap_b256_write(heap, iter, value);
      var new_mem := this.(heap := new_heap);
  
      assert (this.(heap := new_heap)).stack_inv(new_flat) by {
        forall n | 0 <= n < STACK_MAX_WORDS()
          ensures flat_read_32(flat, stack_index_to_ptr(n))
            == 
          flat_read_32(new_flat, stack_index_to_ptr(n))
        {
          var ptr := stack_index_to_ptr(n);
          if flat[ptr] != new_flat[ptr] {
            assert heap_256_inv(heap, flat, iter.base_ptr, iter.index);
            assert false;
          }
        }
        reveal get_stack();
      }
    }

    lemma heap_b256_write_preserves_w32_inv(
      flat: flat_t, new_flat: flat_t,
      iter: b256_iter, value: uint256, other_ptr: nat)

      requires inv(flat)
      requires b256_iter_safe(heap, iter)
      requires new_flat == flat_write_256(flat, iter.cur_ptr(), value)
      requires heap_w32_ptr_valid(heap, other_ptr)

      ensures heap_w32_inv(heap_b256_write(heap, iter, value), new_flat, other_ptr)
    {
      if flat[other_ptr] != new_flat[other_ptr] {
        assert heap_256_inv(heap, flat, iter.base_ptr, iter.index);
        assert false;
      }
    }
  
    lemma heap_b256_write_preverses_inv(
      flat: flat_t, new_flat: flat_t,
      iter: b256_iter, value: uint256)

      requires inv(flat)
      requires b256_iter_safe(heap, iter)
      requires new_flat == flat_write_256(flat, iter.cur_ptr(), value)

      ensures this.(heap := heap_b256_write(heap, iter, value)).inv(new_flat)
    {
      var new_heap := heap_b256_write(heap, iter, value);
      var new_mem := this.(heap := new_heap);

      forall base_ptr | heap_b256_ptr_valid(new_heap, base_ptr)
        ensures heap_b256_inv(new_heap, new_flat, base_ptr)
      {
        heap_b256_write_preserves_b256_inv(flat, new_flat, iter, value, base_ptr);
      }
      forall base_ptr | heap_w32_ptr_valid(new_heap, base_ptr)
        ensures heap_w32_inv(new_heap, new_flat, base_ptr)
      {
        heap_b256_write_preserves_w32_inv(flat, new_flat, iter, value, base_ptr);
      }

      heap_b256_write_preserves_stack_inv(
        flat, new_flat, iter, value);
    }

    lemma heap_w32_write_preserves_b256_inv(
      flat: flat_t, new_flat: flat_t,
      write_ptr: nat, value: uint32, other_ptr: nat)

      requires inv(flat)
      requires heap_w32_ptr_valid(heap, write_ptr)
      requires new_flat == flat_write_32(flat, write_ptr, value)

      requires heap_b256_ptr_valid(heap, other_ptr)

      ensures heap_b256_inv(heap_w32_write(heap, write_ptr, value), new_flat, other_ptr)
    {
      var new_heap := heap_w32_write(heap, write_ptr, value);
      assert heap_b256_inv(heap, flat, other_ptr);
      var buff := heap[other_ptr].b256;
      forall i | 0 <= i < |buff| 
        ensures heap_256_inv(new_heap, new_flat, other_ptr, i)
      {
        assert heap_256_inv(heap, flat, other_ptr, i);
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

      forall base_ptr | heap_b256_ptr_valid(new_heap, base_ptr)
        ensures heap_b256_inv(new_heap, new_flat, base_ptr)
      {
        heap_w32_write_preserves_b256_inv(flat, new_flat, write_ptr, value, base_ptr);
      }
      forall base_ptr | heap_w32_ptr_valid(new_heap, base_ptr)
        ensures heap_w32_inv(new_heap, new_flat, base_ptr)
      {
        heap_w32_write_preserves_w32_inv(flat, new_flat, write_ptr, value, base_ptr);
      }
      heap_w32_write_preserves_stack_inv(flat, new_flat, value, write_ptr);
    }

    lemma stack_write_preserves_b256_inv(
      flat: flat_t, new_flat: flat_t,
      index: nat, value: uint32, base_ptr: nat)

      requires inv(flat)
      requires index < |stack|
      requires new_flat == flat_write_32(flat, stack_index_to_ptr(index), value)
      requires heap_b256_ptr_valid(heap, base_ptr)
  
      ensures heap_b256_inv(heap, new_flat, base_ptr)
    {
      var buff := heap[base_ptr].b256;
      var new_buff := heap[base_ptr].b256;
  
      forall i | 0 <= i < |new_buff|
        ensures heap_256_inv(heap, new_flat, base_ptr, i) 
      {
        assert heap_256_inv(heap, flat, base_ptr, i);
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
      forall base_ptr | heap_b256_ptr_valid(heap, base_ptr)
        ensures heap_b256_inv(heap, new_flat, base_ptr)
      {
        stack_write_preserves_b256_inv(flat, new_flat, index, value, base_ptr);
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

    predicate inv(flat: flat_t)
    {
      && stack_addrs_valid(flat)
      && as_imem(flat).inv(flat)
      && frames.frames_inv(get_stack(flat))
    }

    function push(flat: flat_t, num_words: uint32): mem_t
      requires inv(flat)
      requires in_stack_addr_range(frames.sp - num_words * 4)
    {
      var stack := get_stack(flat);
      this.(frames := frames.push(num_words, stack))
    }

    lemma push_preserves_inv(flat: flat_t, num_words: uint32)
      requires push.requires(flat, num_words)
      ensures push(flat, num_words).inv(flat)
    {
      frames.push_preserves_inv(num_words, get_stack(flat));
    }

    lemma heap_b256_write_preverses_inv(
      flat: flat_t, iter: b256_iter, value: uint256)

      requires inv(flat)
      requires b256_iter_safe(heap, iter)

      ensures this.(heap := heap_b256_write(heap, iter, value)).
        inv(flat_write_256(flat, iter.cur_ptr(), value))
    {
      var new_flat := flat_write_256(flat, iter.cur_ptr(), value);
      as_imem(flat).heap_b256_write_preverses_inv(flat, new_flat,
        iter, value);
    }

    lemma heap_w32_write_preverses_inv(
      flat: flat_t, write_ptr: nat, value: uint32)
    
      requires inv(flat)
      requires heap_w32_ptr_valid(heap, write_ptr)
      ensures this.(heap := heap_w32_write(heap, write_ptr, value)).
        inv(flat_write_32(flat, write_ptr, value))
    {
      var new_flat := flat_write_32(flat, write_ptr, value);
      as_imem(flat).heap_w32_write_preverses_inv(flat, new_flat,
        write_ptr, value);
    }

    function frames_write(index: nat, value: uint32): mem_t
      requires frames.write.requires(index, value)
    {
      this.(frames := frames.write(index, value))
    }

    lemma frames_write_preverses_inv(
      flat: flat_t, index: nat, value: uint32)
    
      requires inv(flat)
      requires frames.write.requires(index, value)

      ensures in_stack_addr_range(frames.sp + index * 4)
      ensures frames_write(index, value).
        inv(flat_write_32(flat, frames.sp + index * 4, value))
    {
      var new_mem := frames_write(index, value);
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
}