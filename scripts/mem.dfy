include "../lib/generic_bv_ops.dfy"

module memory32 {
  import opened integers

  const DMEM_LIMIT: int := 0x8000

  // basic map
  type mem_t = map<int, uint32>


  predicate method uint32_ptr_admissible(ptr: nat)
  {
    // uint32 ptr should be 4 bytes aligned
    && ptr % 4 == 0
    && (ptr + 4) <= DMEM_LIMIT
  }

  predicate method uint32_ptr_valid(mem: mem_t, ptr: nat)
  {
    && uint32_ptr_admissible(ptr)
    && ptr + 0 in mem
  }

  // this assumes little endiness
  function method {:opaque} uint32_sel_uint32(x: uint32, sel: nat): uint32
    requires sel < 1
  {
    if sel == 0 then ((x as bv32) as int) % BASE_32
    else ((x as bv32 >> 0) as int) % BASE_32
  }

  function method {:opaque} uint32_asm_uint32(
    p0: uint32): uint32
  {
    ((p0 as bv32)) as uint32
  }

  function method uint32_read(mem: mem_t, ptr: nat): uint32
    requires uint32_ptr_valid(mem, ptr)
  {
    var p0 := mem[ptr + 0];
    uint32_asm_uint32(p0)
  }



  predicate method uint256_ptr_admissible(ptr: nat)
  {
    // uint256 ptr should be 32 bytes aligned
    && ptr % 32 == 0
    && (ptr + 32) <= DMEM_LIMIT
  }

  predicate method uint256_ptr_valid(mem: mem_t, ptr: nat)
  {
    && uint256_ptr_admissible(ptr)
    && ptr + 0 in mem
    && ptr + 4 in mem
    && ptr + 8 in mem
    && ptr + 12 in mem
    && ptr + 16 in mem
    && ptr + 20 in mem
    && ptr + 24 in mem
    && ptr + 28 in mem
  }

  // this assumes little endiness
  function method {:opaque} uint256_sel_uint32(x: uint256, sel: nat): uint32
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

  function method {:opaque} uint32_asm_uint256(
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

  function method uint256_read(mem: mem_t, ptr: nat): uint256
    requires uint256_ptr_valid(mem, ptr)
  {
    var p0 := mem[ptr + 0];
    var p1 := mem[ptr + 4];
    var p2 := mem[ptr + 8];
    var p3 := mem[ptr + 12];
    var p4 := mem[ptr + 16];
    var p5 := mem[ptr + 20];
    var p6 := mem[ptr + 24];
    var p7 := mem[ptr + 28];
    uint32_asm_uint256(p0, p1, p2, p3, p4, p5, p6, p7)
  }






}
