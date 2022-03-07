include "../../lib/generic_bv_ops.dfy"

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

  function method flat_read_32(flat: flat_t, ptr: nat): uint32
    requires ptr_admissible_32(ptr)
  {
    if ptr in flat then flat[ptr] else 0
  }

  function method flat_write_32(flat: flat_t, ptr: nat, x: uint32): (new_flat: flat_t) 
    requires ptr_admissible_32(ptr)
    ensures flat_ptr_valid_32(new_flat, ptr)
  {
    flat
    [ptr + 0 := x]
  }

  lemma flat_read_write_basic_32(flat: flat_t, x: uint32, ptr: nat)
    requires ptr_admissible_32(ptr)
    ensures flat_read_32(flat_write_32(flat, ptr, x), ptr) == x
  {
    var new_flat := flat_write_32(flat, ptr, x);
    assert flat_read_32(new_flat, ptr) == x;
  }
  predicate method ptr_admissible_256(ptr: nat)
  {
    // uint256 ptr should be 32 bytes aligned
    && ptr % 32 == 0
    && (ptr + 32) < DMEM_LIMIT
  }

  predicate method flat_ptr_valid_256(flat: flat_t, ptr: nat)
  {
    && ptr_admissible_256(ptr)
    && ptr + 0 in flat
    && ptr + 4 in flat
    && ptr + 8 in flat
    && ptr + 12 in flat
    && ptr + 16 in flat
    && ptr + 20 in flat
    && ptr + 24 in flat
    && ptr + 28 in flat
  }

  function method {:opaque} select_32_from_256(x: uint256, sel: nat): uint32
    requires sel < 8
  {
    if sel == 0 then ((x as bv256) as int) % BASE_32
    else if sel == 1 then ((x as bv256 >> 32) as int) % BASE_32
    else if sel == 2 then ((x as bv256 >> 64) as int) % BASE_32
    else if sel == 3 then ((x as bv256 >> 96) as int) % BASE_32
    else if sel == 4 then ((x as bv256 >> 128) as int) % BASE_32
    else if sel == 5 then ((x as bv256 >> 160) as int) % BASE_32
    else if sel == 6 then ((x as bv256 >> 192) as int) % BASE_32
    else ((x as bv256 >> 224) as int) % BASE_32
  }

  function method {:opaque} assemble_32_to_256(
    p0: uint32, 
    p1: uint32, 
    p2: uint32, 
    p3: uint32, 
    p4: uint32, 
    p5: uint32, 
    p6: uint32, 
    p7: uint32): uint256
  {
    ((p0 as bv256)
    |(p1 as bv256 << 32)
    |(p2 as bv256 << 64)
    |(p3 as bv256 << 96)
    |(p4 as bv256 << 128)
    |(p5 as bv256 << 160)
    |(p6 as bv256 << 192)
    |(p7 as bv256 << 224)) as uint256
  }

  lemma {:axiom} value_256_from_32(x: uint256)
    ensures x == assemble_32_to_256(
      select_32_from_256(x, 0), 
      select_32_from_256(x, 1), 
      select_32_from_256(x, 2), 
      select_32_from_256(x, 3), 
      select_32_from_256(x, 4), 
      select_32_from_256(x, 5), 
      select_32_from_256(x, 6), 
      select_32_from_256(x, 7));

  function method flat_read_256(flat: flat_t, ptr: nat): uint256
    requires ptr_admissible_256(ptr)
  {
    var p0 := flat_read_32(flat, ptr + 0);
    var p1 := flat_read_32(flat, ptr + 4);
    var p2 := flat_read_32(flat, ptr + 8);
    var p3 := flat_read_32(flat, ptr + 12);
    var p4 := flat_read_32(flat, ptr + 16);
    var p5 := flat_read_32(flat, ptr + 20);
    var p6 := flat_read_32(flat, ptr + 24);
    var p7 := flat_read_32(flat, ptr + 28);
    assemble_32_to_256(p0, p1, p2, p3, p4, p5, p6, p7)
  }

  function method flat_write_256(flat: flat_t, ptr: nat, x: uint256): (new_flat: flat_t) 
    requires ptr_admissible_256(ptr)
    ensures flat_ptr_valid_256(new_flat, ptr)
  {
    flat
    [ptr + 0 := select_32_from_256(x, 0)]
    [ptr + 4 := select_32_from_256(x, 1)]
    [ptr + 8 := select_32_from_256(x, 2)]
    [ptr + 12 := select_32_from_256(x, 3)]
    [ptr + 16 := select_32_from_256(x, 4)]
    [ptr + 20 := select_32_from_256(x, 5)]
    [ptr + 24 := select_32_from_256(x, 6)]
    [ptr + 28 := select_32_from_256(x, 7)]
  }

  lemma flat_read_write_basic_256(flat: flat_t, x: uint256, ptr: nat)
    requires ptr_admissible_256(ptr)
    ensures flat_read_256(flat_write_256(flat, ptr, x), ptr) == x
  {
    var new_flat := flat_write_256(flat, ptr, x);
    value_256_from_32(x);
    assert flat_read_256(new_flat, ptr) == x;
  }

}