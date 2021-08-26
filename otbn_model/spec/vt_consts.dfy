include "../libraries/src/NativeTypes.dfy"

module vt_consts {
    import opened NativeTypes

    const BASE_192: int := 0x1_00000000_00000000_00000000_00000000_00000000_00000000

    const DMEM_LIMIT: int := 0x8000
    const NUM_WORDS:  int := 12

    // ignore the mapping
    const NA :int := -1;
}