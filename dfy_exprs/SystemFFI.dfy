// https://github.com/wilcoxjay/notes
include "NativeTypes.dfy"

import opened NativeTypes

class SystemFFI
{
    // static method{:axiom} GetRandomBV(length: uint32) returns (buffer: array<byte>)
    //     requires length > 0;
    //     ensures buffer.Length != 0;

    static method{:axiom} GetRandomBit() returns (b: bit)
}