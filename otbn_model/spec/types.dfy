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

/////////////////
// Bignum
/////////////////
	
datatype Bignum = Bignum(l7:uint32, l6:uint32, l5:uint32, l4:uint32, l3:uint32, l2:uint32, l1:uint32, l0:uint32)

} // end module types
