module types {

/////////////////
// Native types
/////////////////

newtype{:nativeType "byte"} byte = i:int | 0 <= i < 0x100
newtype{:nativeType "uint"} uint = i:int | 0 <= i < 0x1_0000_0000
newtype{:nativeType "ulong"} ulong = i:int | 0 <= i < 0x1_0000_0000_0000_0000

/////////////////
// Subset types
/////////////////
type uint8   = i:int | 0 <= i < 0x100
type uint16  = i:int | 0 <= i < 0x10000
type uint32  = i:int | 0 <= i < 0x1_0000_0000
type uint64  = i:int | 0 <= i < 0x1_0000_0000_0000_0000
type uint128 = i:int | 0 <= i < 0x1_00000000_00000000_00000000_00000000
	
type uint256 = i:int | 0 <= i < 0x1_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000
type Bignum = uint256
const BignumSize : int := 115792089237316195423570985008687907853269984665640564039457584007913129639936

/////////////////
// BitsOfByte
/////////////////

newtype twobits = i:int | 0 <= i < 4
datatype BitsOfByte = BitsOfByte(lo:twobits,
                                 mid_lo:twobits,
                                 mid_hi:twobits,
                                 hi:twobits)

function bits_to_byte(bits:BitsOfByte) : uint8
{
    64 * (bits.hi as uint8) + 16 * (bits.mid_hi as uint8) + 4 * (bits.mid_lo as uint8) + (bits.lo as uint8)
}

function byte_to_bits(b:uint8) : BitsOfByte
{
    BitsOfByte((b % 4) as twobits, ((b / 4) % 4) as twobits, ((b / 16) % 4) as twobits, ((b / 64) % 4) as twobits)
}

/////////////////
// Bit vectors
/////////////////

function method {:opaque} BitsToWord(b:bv32) : uint32 { b as uint32 }
function method {:opaque} WordToBits(w:uint32) : bv32 { w as bv32 }

function method {:opaque} BitsToBignum(b:bv256) : uint256 { b as uint256 }
function method {:opaque} BignumToBits(bn:uint256) : bv256 { bn as bv256 }

function method {:opaque} BoolToBits(bl:bool) : bv256
{
	if bl then 1 as bv256 else 0 as bv256
}

lemma {:axiom} lemma_BitsToWordToBits(b:bv32)
    ensures WordToBits(BitsToWord(b)) == b;

lemma {:axiom} lemma_WordToBitsToWord(w:uint32)
    ensures BitsToWord(WordToBits(w)) == w;

lemma {:axiom} lemma_BitsToBignumToBits(b:bv256)
    ensures BignumToBits(BitsToBignum(b)) == b;

lemma {:axiom} lemma_BignumToBitsToBignum(bn:uint256)
    ensures BitsToBignum(BignumToBits(bn)) == bn;
	
} // end module types
