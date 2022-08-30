include "../../bvop/bv_op.s.dfy"

module flat {
  import opened integers

  const DMEM_LIMIT: int := 0x80000

  // basic map
  type flat_t = map<int, uint32>


  predicate method ptr_admissible_32(ptr: nat)
  {
    // uint32 ptr should be 4 bytes aligned
    && ptr % 4 == 0
    && (ptr + 4) < DMEM_LIMIT
  }

  predicate method flat_ptr_valid_32(flat: flat_t, ptr: nat)
  {
    && ptr_admissible_32(ptr)
    && ptr + 0 in flat
  }

  function method {:opaque} select_32_from_32(x: uint32, sel: nat): uint32
    requires sel < 1
  {
    if sel == 0 then ((x as bv32) as int) % BASE_32
    else ((x as bv32 >> 0) as int) % BASE_32
  }

  function method {:opaque} assemble_32_to_32(
    p0: uint32): uint32
  {
    ((p0 as bv32)) as uint32
  }

  lemma {:axiom} value_32_from_32(x: uint32)
    ensures x == assemble_32_to_32(
      select_32_from_32(x, 0));

  function method flat_read_32(flat: flat_t, ptr: nat): uint32
    requires ptr_admissible_32(ptr)
  {
    if ptr in flat then flat[ptr] else 0
  }

  function method flat_write_32(flat: flat_t, ptr: nat, x: uint32): (new_flat: flat_t) 
    requires ptr_admissible_32(ptr)
    ensures flat_ptr_valid_32(new_flat, ptr)
  {
    flat[ptr := x]
  }

  lemma flat_read_write_basic_32(flat: flat_t, x: uint32, ptr: nat)
    requires ptr_admissible_32(ptr)
    ensures flat_read_32(flat_write_32(flat, ptr, x), ptr) == x
  {
    var new_flat := flat_write_32(flat, ptr, x);
    value_32_from_32(x);
    assert flat_read_32(new_flat, ptr) == x;
  }

}