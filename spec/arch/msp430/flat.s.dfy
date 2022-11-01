// include "../../bvop/bv_op.s.dfy"

// module flat {
//   import opened integers

//   const DMEM_LIMIT: int := 0x10000

//   // basic map
//   type flat_t = map<int, uint16>


//   predicate method ptr_admissible_16(ptr: nat)
//   {
//     // uint16 ptr should be 2 bytes aligned
//     && ptr % 2 == 0
//     && (ptr + 2) < DMEM_LIMIT
//   }

//   predicate method flat_ptr_valid_16(flat: flat_t, ptr: nat)
//   {
//     && ptr_admissible_16(ptr)
//     && ptr + 0 in flat
//   }

//   function method {:opaque} select_16_from_16(x: uint16, sel: nat): uint16
//     requires sel < 1
//   {
//     if sel == 0 then ((x as bv16) as int) % BASE_16
//     else ((x as bv16 >> 0) as int) % BASE_16
//   }

//   function method {:opaque} assemble_16_to_16(
//     p0: uint16): uint16
//   {
//     ((p0 as bv16)) as uint16
//   }

//   lemma {:axiom} value_16_from_16(x: uint16)
//     ensures x == assemble_16_to_16(
//       select_16_from_16(x, 0));

//   function method flat_read_16(flat: flat_t, ptr: nat): uint16
//     requires ptr_admissible_16(ptr)
//   {
//     if ptr in flat then flat[ptr] else 0
//   }

//   function method flat_write_16(flat: flat_t, ptr: nat, x: uint16): (new_flat: flat_t) 
//     requires ptr_admissible_16(ptr)
//     ensures flat_ptr_valid_16(new_flat, ptr)
//   {
//     flat[ptr := x]
//   }

//   lemma flat_read_write_basic_16(flat: flat_t, x: uint16, ptr: nat)
//     requires ptr_admissible_16(ptr)
//     ensures flat_read_16(flat_write_16(flat, ptr, x), ptr) == x
//   {
//     var new_flat := flat_write_16(flat, ptr, x);
//     value_16_from_16(x);
//     assert flat_read_16(new_flat, ptr) == x;
//   }

// }