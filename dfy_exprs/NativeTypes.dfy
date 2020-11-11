module NativeTypes {
    type uint1 = i: int | 0 <= i < 2
    type uint32 = i:int | 0 <= i < 0x100000000

    newtype{:nativeType "byte"} bit = i:int | 0 <= i < 2
    newtype{:nativeType "int"} int32 = i:int | -0x80000000 <= i < 0x80000000
}