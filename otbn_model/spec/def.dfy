// Trusted specification for the OpenTitan Bignum semantics

include "types.dfy"

module bignum_def {

import opened types

// General purpose and control registers, 32b
datatype Reg32 =
| Gpr(x:int)
| Rnd // Random number

// Wide data and special registers, 256b
datatype Reg256 =
| Wdr(w:int)
| WMod // Wide modulo register
| WRnd // Wide random number

datatype ins32 =
| ADD32(xrd:Reg32, xrs1:Reg32, xrs2:Reg32)
| ADDI32(xrd:Reg32, xrs1:Reg32, imm:uint32)
| LUI32(xrd:Reg32, imm:uint32)
| SUB32(xrd:Reg32, xrs1:Reg32, xrs2:Reg32)
| AND32(xrd:Reg32, xrs1:Reg32, xrs2:Reg32)
| ANDI32(xrd:Reg32, xrs1:Reg32, imm:uint32)
| OR32(xrd:Reg32, xrs1:Reg32, xrs2:Reg32)
| ORI32(xrd:Reg32, xrs1:Reg32, imm:uint32)
| XOR32(xrd:Reg32, xrs1:Reg32, xrs2:Reg32)
| XORI32(xrd:Reg32, xrs1:Reg32, imm:uint32)
| LW // TODO
| SW // TODO
| BEQ32(xrs1:Reg32, xrs2:Reg32, offset:uint32)
| BNE32(xrs1:Reg32, xrs2:Reg32, offset:uint32)
| LOOP32(xrs1:Reg32, bodysize:uint32)
| LOOPI32(iterations:uint32, bodysize:uint32)
| JAL32(xrd:Reg32, offset:uint32)
| JALR32(xrd:Reg32, xrs1:Reg32, offset:uint32)
| CSRRS32(xrd:Reg32, csr:uint32, xrs2:Reg32)
| ECALL // TODO

datatype ins256 =
| ADD256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:Bignum, flg:bool)
| ADDC256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:Bignum, flg:bool)
| ADDI256(wrd:Reg256, wrs1:Reg256, imm:Bignum, flg:bool)
| ADDM256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256)
| MULQACC
| MULH256(wrd:Reg256, wrs1:Reg256, hw1:bool, wrs2:Reg256, hw2:bool)
| SUB256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:Bignum, flg:bool)
| SUBB256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:Bignum, flg:bool)
| SUBI256(wrd:Reg256, wrs1:Reg256, imm:Bignum, flg:bool)
| SUBM256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256)
| AND256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:Bignum)
| OR256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:Bignum)
| NOT256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:Bignum)
| XOR256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:Bignum, flg:bool)
| RSHI256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, imm:Bignum)
| SEL256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, flg:bool)
| CMP256(wrs1:Reg256, wrs2:Reg256, flg:bool)
| CMPB256(wrs1:Reg256, wrs2:Reg256, flg:bool)
| LID // TODO
| SID // TODO
| MOV256(wrd:Reg256, wrs:Bignum)
| MOVR // TODO
| WSRRS // TODO
| WSRRW // TODO

datatype codes = CNil | va_CCons(hd:code, tl:codes)

datatype code =
| Ins32(ins:ins32)
| Ins256(bn_ins:ins256)
| Block(block:codes)

type Frame = map<int, uint32>
type Stack = seq<Frame>

datatype state = state(
	 xregs: map<Reg32, uint32>, // 32-bit registers
	 wregs: map<Reg256, Bignum>, // 256-bit registers
	 //flags: map<int, bool>,
	 stack: Stack,
	 ok: bool)

predicate IsUInt32(i:int) { 0 <= i < 0x1_0000_0000 }

predicate ValidRegister32(xregs:map<Reg32, uint32>, r:Reg32)
{
	r in xregs
}

function eval_xreg(xregs:map<Reg32, uint32>, r:Reg32) : uint32
{
	if !ValidRegister32(xregs, r) then 24
	else xregs[r]
}

predicate ValidRegisterIndex(index:int)
{
	0 <= index < 32
}

predicate ValidSourceRegister32(s:state, r:Reg32)
{
	if r.Rnd? then
		ValidRegister32(s.xregs, r)
	else
		ValidRegister32(s.xregs, r) && ValidRegisterIndex(r.x)
}

predicate ValidDestinationRegister32(s:state, r:Reg32)
{
		!r.Rnd? && ValidRegister32(s.xregs, r) && ValidRegisterIndex(r.x)
}

function eval_reg32(s:state, r:Reg32) : uint32
{
	if !ValidSourceRegister32(s, r) then
		42
	else
		s.xregs[r]
}

predicate evalIns32(xins:ins32, s:state, r:state)
{
	// TODO: actual implementation
	if !s.ok then
		!r.ok
	else
		r.ok
}

predicate evalIns256(wins:ins256, s:state, r:state)
{
	// TODO: actual implementation
	if !s.ok then
		!r.ok
	else
		r.ok
}

predicate evalBlock(block:codes, s:state, r:state)
{
    if block.CNil? then
        r == s
    else
        exists r':state :: evalCode(block.hd, s, r') && evalBlock(block.tl, r', r)
}

predicate evalCode(c:code, s:state, r:state)
    decreases c, 0
{
    match c
        case Ins32(ins) => evalIns32(ins, s, r)
        case Ins256(ins) => evalIns256(ins, s, r)
        case Block(block) => evalBlock(block, s, r)
        //case IfElse(cond, ifT, ifF) => evalIfElse(cond, ifT, ifF, s, r)
        //case While(cond, body) => exists n:nat :: evalWhile(cond, body, n, s, r)
}

}
