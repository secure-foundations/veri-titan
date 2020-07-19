module NativeTypes {
 	newtype{:nativeType "sbyte"} int8 = i:int | -0x80 <= i < 0x80
 	newtype{:nativeType "byte"} uint8 = i:int | 0 <= i < 0x100
 	newtype{:nativeType "short"} int16 = i:int | -0x8000 <= i < 0x8000
 	newtype{:nativeType "ushort"} uint16 = i:int | 0 <= i < 0x10000
 	newtype{:nativeType "int"} int32 = i:int | -0x80000000 <= i < 0x80000000
 	newtype{:nativeType "uint"} uint32 = i:int | 0 <= i < 0x100000000
 	newtype{:nativeType "long"} int64 = i:int | -0x8000000000000000 <= i < 0x8000000000000000
 	newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x10000000000000000
 	newtype{:nativeType "sbyte"} nat8 = i:int | 0 <= i < 0x80
 	newtype{:nativeType "short"} nat16 = i:int | 0 <= i < 0x8000
 	newtype{:nativeType "int"} nat32 = i:int | 0 <= i < 0x80000000
 	newtype{:nativeType "long"} nat64 = i:int | 0 <= i < 0x8000000000000000
  
 	type uint2 = i: int | 0 <= i < 2

 	const UINT64_MAX :uint64 := 0xffffffffffffffff;
 	const UINT32_MAX :uint32 := 0xffffffff;
 	const UINT16_MAX :uint16 := 0xffff;
 	const INT64_MAX : int64 := 0x7fffffffffffffff;
 	const INT64_MIN : int64 := -0x7fffffffffffffff; // what?

 	type uint128 = i:int | 0 <= i < 0x100000000000000000000000000000000
 	type uint256 = i:int | 0 <= i < 0x10000000000000000000000000000000000000000000000000000000000000000
 	const UINT128_MAX :uint128 := 0xffffffffffffffffffffffffffffffff;

 	function method {:extern "NativeTypes", "xor8"} xor8(x:uint8, y:uint8) : uint8

 	function method {:extern "NativeTypes", "xor16"} xor16(x:uint16, y:uint16) : uint16
 	function method {:extern "NativeTypes", "xor32"} xor32(x:uint32, y:uint32) : uint32
 	function method {:extern "NativeTypes", "xor64"} xor64(x:uint64, y:uint64) : uint64

 	function method {:extern "NativeTypes", "or8"} or8(x:uint8, y:uint8) : uint8
 	function method {:extern "NativeTypes", "or16"} or16(x:uint16, y:uint16) : uint16
 	function method {:extern "NativeTypes", "or32"} or32(x:uint32, y:uint32) : uint32
 	function method {:extern "NativeTypes", "or64"} or64(x:uint64, y:uint64) : uint64

 	function method {:extern "NativeTypes", "and8"} and8(x:uint8, y:uint8) : (r:uint8)
		ensures r <= x;
		ensures r <= y;

 	function method {:extern "NativeTypes", "and16"} and16(x:uint16, y:uint16) : uint16
 	function method {:extern "NativeTypes", "and32"} and32(x:uint32, y:uint32) : uint32
 	function method {:extern "NativeTypes", "and64"} and64(x:uint64, y:uint64) : (r:uint64)
 	  ensures r <= x && r <= y && (r == x || r == y);

 	function method {:extern "NativeTypes", "lshift8"} lshift8(x:uint8, y:uint8) : uint8
 	function method {:extern "NativeTypes", "lshift16"} lshift16(x:uint16, y:uint16) : uint16
 	function method {:extern "NativeTypes", "lshift32"} lshift32(x:uint32, y:uint32) : uint32
 	function method {:extern "NativeTypes", "lshift64"} lshift64(x:uint64, y:uint64) : uint64

 	function method {:extern "NativeTypes", "not64"} not64(x:uint64) : uint64

 	// Compute max of two values
 	function method maxi64 (x:int64, y:int64): (r:int64)
		ensures r >= x;
		ensures r >= y;
 	{
 	 	if x > y then x else y
 	}

 	// Compute max of two values
 	function method maxu64 (x:uint64, y:uint64): (r:uint64)
		ensures r >= x;
		ensures r >= y;
 	{
 	 	if x > y then x else y
 	}

 	// Compute min of two values
 	function method minu32 (x:uint32, y:uint32): (r:uint32)
		ensures r <= x;
		ensures r <= y;
 	{
 	 	if x > y then y else x
 	}

 	// Compute min of two values
 	function method minu64 (x:uint64, y:uint64): (r:uint64)
		ensures r <= x;
		ensures r <= y;
 	{
 	 	if x > y then y else x
 	}

 	method {:extern "NativeTypes", "split64"} split64(x: uint64) returns (lower: uint32, upper: uint32)
 	 	ensures upper as int * (UINT32_MAX as int + 1) + lower as int == x as int;

 	function method lh64(x: uint64) : (r: uint32)

 	function method uh64(x: uint64) : (r: uint32)

 	lemma split64_lemma(x: uint64)
 	 	ensures uh64(x) as int * (UINT32_MAX as int + 1) + lh64(x) as int == x as int;
 	 	ensures lh64(x) as int == x as int % (UINT32_MAX as int + 1);

 	function method reinterp64(a: int64) : (b: uint64)
		ensures a >= 0 ==> (
			&& a as int == b as int
			&& b as int <= UINT32_MAX as int); // this should be provable
		ensures a < 0 ==> (
			&& reinterp64(a) as int - a as int == UINT64_MAX as int + 1
			&& uh64(b) == UINT32_MAX); // this should be provable
}
