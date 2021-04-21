module types {

const BASE_1:   int := 0x2
const BASE_2:   int := 0x4
const BASE_4:   int := 0x1_0
const BASE_8:   int := 0x1_00
const BASE_16:  int := 0x1_0000
const BASE_32:  int := 0x1_00000000
const BASE_64:  int := 0x1_00000000_00000000
const BASE_128: int := 0x1_00000000_00000000_00000000_00000000
const BASE_192: int := 0x1_00000000_00000000_00000000_00000000_00000000_00000000
const BASE_256: int := 0x1_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000

type uint1   = i :int | 0 <= i < BASE_1
type uint2   = i :int | 0 <= i < BASE_2
type uint4   = i :int | 0 <= i < BASE_4
type uint8   = i :int | 0 <= i < BASE_8
type uint16  = i :int | 0 <= i < BASE_16
type uint32  = i :int | 0 <= i < BASE_32
type uint64  = i :int | 0 <= i < BASE_64
type uint128 = i :int | 0 <= i < BASE_128
type uint256 = i :int | 0 <= i < BASE_256

const DMEM_LIMIT: int := 0x8000

function method {:opaque} to_uint32(b:bv32) : uint32 { b as uint32 }
function method {:opaque} to_bv32(w:uint32) : bv32 { w as bv32 }

function method {:opaque} to_uint256(b:bv256) : uint256 { b as uint256 }
function method {:opaque} to_bv256(bn:uint256) : bv256 { bn as bv256 }

lemma {:axiom} lemma_to_uint32(b:bv32)
    ensures to_bv32(to_uint32(b)) == b;

lemma {:axiom} lemma_to_bv32(w:uint32)
    ensures to_uint32(to_bv32(w)) == w;

lemma {:axiom} lemma_to_uint256(b:bv256)
    ensures to_bv256(to_uint256(b)) == b;

lemma {:axiom} lemma_to_bv256(bn:uint256)
    ensures to_uint256(to_bv256(bn)) == bn;

} // end module types
