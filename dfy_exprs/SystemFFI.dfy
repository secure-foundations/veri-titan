// https://github.com/wilcoxjay/notes

newtype{:nativeType "byte"} byte = i:int | 0 <= i < 8
newtype{:nativeType "int"} int32 = i:int | -0x80000000 <= i < 0x80000000

class SystemFFI
{
    static method{:axiom} GetRandomBV(length: int32) returns (buffer: array<byte>)
}