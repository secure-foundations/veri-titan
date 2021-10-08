include "../libraries/src/BoundedInts.dfy"

module vt_consts {
    import BoundedInts

    const BASE_192: int := 0x1_00000000_00000000_00000000_00000000_00000000_00000000

    const BASE_1   : int := BoundedInts.TWO_TO_THE_1
    const BASE_2   : int := BoundedInts.TWO_TO_THE_2
    const BASE_4   : int := BoundedInts.TWO_TO_THE_4
    const BASE_5   : int := BoundedInts.TWO_TO_THE_5
    const BASE_8   : int := BoundedInts.TWO_TO_THE_8
    const BASE_16  : int := BoundedInts.TWO_TO_THE_16
    const BASE_32  : int := BoundedInts.TWO_TO_THE_32
    const BASE_64  : int := BoundedInts.TWO_TO_THE_64
    const BASE_128 : int := BoundedInts.TWO_TO_THE_128
    const BASE_256 : int := BoundedInts.TWO_TO_THE_256
    const BASE_512 : int := BoundedInts.TWO_TO_THE_512

    const DMEM_LIMIT: int := 0x8000
    const NUM_WORDS:  int := 12

    // ignore the mapping
    const NA :int := -1;
}