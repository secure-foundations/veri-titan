include "types.dfy"
include "../lib/powers.dfy"

module ops {
	import opened types
	import opened powers

	function method {:opaque} uint32_and(x:uint32, y:uint32) : uint32
	{
        (x as bv32 & y as bv32) as uint32
	}

	function method {:opaque} uint32_or(x:uint32, y:uint32):uint32
	{
        (x as bv32 | y as bv32) as uint32
	}

	function method {:opaque} uint32_not(x:uint32) : uint32
	{
		!(x as bv32) as uint32
	}

	function method {:opaque} uint32_xor(x:uint32, y:uint32) : uint32
	{
        (x as bv32 ^ y as bv32) as uint32
	}

	function method {:opaque} uint32_rs(x:uint32, amount:uint32) : uint32
		requires amount < 32;
	{
		(x as bv32 >> amount) as uint32
	}

	function method {:opaque} uint32_ls(x:uint32, amount:uint32) : uint32
		requires amount < 32;
	{
		(x as bv32 << amount) as uint32
	}

	function method {:opaque} uint32_add(x:uint32, y:uint32):uint32
	{
		(x + y) % 0x1_0000_0000
	}

	function method {:opaque} uint32_sub(x:uint32, y:uint32):uint32
	{
		(x - y) % 0x1_0000_0000
	}

  function method {:opaque} to_signed32(x:uint32):int32

  function method {:opaque} uint32_arith_rs(x:uint32, y:uint32):uint32


	function method {:opaque} uint32_se(x:uint32, size:int):uint32
		requires 0 <= size < 32;

} // end module ops
