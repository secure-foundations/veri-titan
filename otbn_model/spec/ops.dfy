include "types.dfy"

	module ops {

		import opened types

		function {:opaque} BitwiseAdd32(x:uint32, y:uint32):uint32
		{
			(x + y) % 0x1_0000_0000
		}

		lemma lemma_BitwiseAdd32EquivalentToAddMod2To32(x:uint32, y:uint32)
			ensures BitwiseAdd32(x, y) == (x + y) % 0x1_0000_0000;
		{
			reveal_BitwiseAdd32();
		}

	}
