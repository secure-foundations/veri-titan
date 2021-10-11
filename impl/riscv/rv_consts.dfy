module rv_consts {

    const DMEM_LIMIT: int := 0x8000
    const NUM_WORDS:  int := 12

    const BASE_1:   int := 2
    const BASE_2:   int := 4
    const BASE_4:   int := 16
    const BASE_5:   int := 32
    const BASE_8:   int := 0x100
    const BASE_16:  int := 0x10000
    const BASE_24:  int := 0x1000000
    const BASE_32:  int := 0x1_00000000
    const BASE_40:  int := 0x100_00000000
    const BASE_48:  int := 0x10000_00000000
    const BASE_56:  int := 0x1000000_00000000
    const BASE_64:  int := 0x1_00000000_00000000
    const BASE_128: int := 0x1_00000000_00000000_00000000_00000000
    const BASE_256: int := 0x1_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000
    const BASE_512: int :=
      0x1_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000;

    const BASE_31:  int := 0x80000000
    const BASE_63:  int := 0x80000000_00000000

    // ignore the mapping
    const NA :int := -1;
}
