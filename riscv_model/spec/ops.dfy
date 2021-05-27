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

	function method {:opaque} uint32_mul(x:uint32, y:uint32):uint32
	{
		(x * y) % 0x1_0000_0000
	}

// multiply and take only the high 32 bits
	function method {:opaque} uint32_mulhu(x:uint32, y:uint32):uint32
  {
    (((x as bv32) * (y as bv32)) as bv64 >> 32) as uint32
  }
  
  // arithmetic right shift
  method {:opaque} uint32_arith_rs(x:uint32, amount:uint32) returns (r:uint32)
    requires amount < 32;
  {
    var s := x % 0x1_0000_0000;
    r := ((x as bv32 >> amount) + (s as bv32 << 31)) as uint32;
  }

// convert the uint32 into a signed integer, and sign-extend
	method {:opaque} uint32_se(x:uint32):uint32

} // end module ops
