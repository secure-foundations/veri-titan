// https://github.com/wilcoxjay/notes

newtype{:nativeType "byte"} byte = i:int | 0 <= i < 2
newtype{:nativeType "int"} int32 = i:int | -0x80000000 <= i < 0x80000000

class SystemFFI
{
    static method{:axiom} GetRandomBV(length: int32) returns (buffer: array<byte>)
        requires length > 0;
        ensures buffer.Length != 0;
    
    static method{:axiom} GetRandomBit() returns (b: byte)
}