// Trusted specification for the OpenTitan Bignum semantics

include "types.dfy"
include "ops.dfy"

module bignum_def {

import opened types
import opened ops	

// General purpose and control registers, 32b
datatype Reg32 =
| Gpr(x:int)
| Rnd // Random number

// Wide data and special registers, 256b
datatype Reg256 =
| Wdr(w:int)
| WMod // Wide modulo register
| WRnd // Wide random number
| WAcc // Wide accumulator

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
| LW32 // TODO
| SW32 // TODO
| BEQ32(xrs1:Reg32, xrs2:Reg32, offset:uint32)
| BNE32(xrs1:Reg32, xrs2:Reg32, offset:uint32)
| LOOP32(xrs1:Reg32, bodysize:uint32)
| LOOPI32(iterations:uint32, bodysize:uint32)
| JAL32(xrd:Reg32, offset:uint32)
| JALR32(xrd:Reg32, xrs1:Reg32, offset:uint32)
| CSRRS32(xrd:Reg32, csr:Reg32, xrs2:Reg32)
| CSRRW32(xrd:Reg32, csr:Reg32, xrs2:Reg32)
| ECALL32 // TODO

datatype ins256 =
| ADD256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint32, flg:bool)
| ADDC256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint32, flg:bool)
| ADDI256(wrd:Reg256, wrs1:Reg256, imm:Bignum, flg:bool)
| ADDM256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256)
| MULQACC256(zero:bool, wrs1:Reg256, qwsel1:uint32, wrs2:Reg256, qwsel2:uint32, shift:uint32)
| MULH256(wrd:Reg256, wrs1:Reg256, hw1:bool, wrs2:Reg256, hw2:bool)
| SUB256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint32, flg:bool)
| SUBB256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint32, flg:bool)
| SUBI256(wrd:Reg256, wrs1:Reg256, imm:Bignum, flg:bool)
| SUBM256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256)
| AND256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint32)
| OR256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint32)
| NOT256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint32)
| XOR256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint32)
| RSHI256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, imm:Bignum)
| SEL256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, flg:bool)
| CMP256(wrs1:Reg256, wrs2:Reg256, flg:bool)
| CMPB256(wrs1:Reg256, wrs2:Reg256, flg:bool)
| LID256 // TODO
| SID256 // TODO
| MOV256(wrd:Reg256, wrs:Reg256)
| MOVR256 // TODO
| WSRRS256 // TODO
| WSRRW256 // TODO

datatype codes = CNil | va_CCons(hd:code, tl:codes)

datatype code =
| Ins32(ins:ins32)
| Ins256(bn_ins:ins256)
| Block(block:codes)

type Frame = map<int, uint32>
type Stack = seq<Frame>

datatype FlagsGroup = FlagsGroup(cf:bool, lsb:bool, msb:bool, zero:bool)
datatype Flags = Flags(fg0:FlagsGroup, fg1:FlagsGroup)

datatype state = state(
	 xregs: map<Reg32, uint32>, // 32-bit registers
	 wregs: map<Reg256, Bignum>, // 256-bit registers
	 flags: Flags,
	 stack: Stack,
	 ok: bool)

function fst(t:(Bignum, FlagsGroup)) : Bignum { t.0 }
function snd(t:(Bignum, FlagsGroup)) : FlagsGroup { t.1 }

predicate IsUInt32(i:int) { 0 <= i < 0x1_0000_0000 }
predicate IsUInt256(i:int) { 0 <= i < 0x1_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000 }

predicate ValidRegister32(xregs:map<Reg32, uint32>, r:Reg32)
{
	r in xregs
}

predicate ValidRegister256(wregs:map<Reg256, uint256>, r:Reg256)
{
	r in wregs
}

predicate ValidCsr32(r:Reg32)
{
	// TODO: Other CSRs are limbs of WMod or flags-- will these ever be used?
	r.Rnd?
}

function eval_xreg(xregs:map<Reg32, uint32>, r:Reg32) : uint32
{
	if !ValidRegister32(xregs, r) then 24 // TODO: better error message
	else xregs[r]
}

function eval_wreg(wregs:map<Reg256, uint256>, r:Reg256) : uint256
{
	if !ValidRegister256(wregs, r) then 24 // TODO: better error message
	else wregs[r]
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
	true
}

predicate ValidSourceRegister256(s:state, r:Reg256)
{
	if r.WRnd? || r.WMod? then
		ValidRegister256(s.wregs, r)
	else
		ValidRegister256(s.wregs, r) && ValidRegisterIndex(r.w)
}

predicate ValidDestinationRegister256(s:state, r:Reg256)
{
		!r.WRnd? && ValidRegister256(s.wregs, r) && ValidRegisterIndex(r.w)
}

function eval_reg256(s:state, r:Reg256) : uint256
{
	if !ValidSourceRegister256(s, r) then
		42
	else
		s.wregs[r]
}

predicate evalIns256(wins:ins256, s:state, r:state)
{
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

function get_flags_group(fg:bool, flags:Flags) : FlagsGroup { if fg then flags.fg1 else flags.fg0 }

function update_fg(b:bool, f:Flags, fg:FlagsGroup) : Flags { if b then f.(fg1 := fg) else f.(fg0 := fg) }

function cf(flags_group:FlagsGroup) : bool { flags_group.cf }

function xor32(x:uint32, y:uint32) : uint32  { BitwiseXor(x, y) }

function or32(x:uint32, y:uint32) : uint32  { BitwiseOr(x, y) }

function and32(x:uint32, y:uint32) : uint32  { BitwiseAnd(x, y) }

function not32(x:uint32) : uint32 { BitwiseNot(x) }

function rol32(x:uint32, amount:uint32) : uint32
    requires 0 <= amount < 32;
{ RotateLeft(x, amount) }

function ror32(x:uint32, amount:uint32) : uint32
    requires 0 <= amount < 32;
    { RotateRight(x, amount) }

function shl32(x:uint32, amount:uint32) : uint32
    requires 0 <= amount < 32;
    { LeftShift(x, amount) }

function shr32(x:uint32, amount:uint32) : uint32
    requires 0 <= amount < 32;
    { RightShift(x, amount) }

function sext32(x:uint32, sz:int) : uint32
  requires 0 < sz < 32;
    { BitwiseSignExtend(x, sz) }

function add256(x:Bignum, y:Bignum, st:bool, sb:uint32, flags_group:FlagsGroup) : (Bignum, FlagsGroup)
	requires sb < 32;
{ var (sum, new_carry) := BignumAddCarry(x, y, st, sb, false); (sum, flags_group.(cf := new_carry))  }

function addc256(x:Bignum, y:Bignum, st:bool, sb:uint32, flags_group:FlagsGroup) : (Bignum, FlagsGroup)
	requires sb < 32;
{ var (sum, new_carry) := BignumAddCarry(x, y, st, sb, cf(flags_group)); (sum, flags_group.(cf := new_carry))  }

function addi256(x:Bignum, imm:Bignum, flags_group:FlagsGroup) : (Bignum, FlagsGroup)
	requires imm < 1024;
{ var (sum, new_carry) := BignumAddCarry(x, imm, false, 0, false); (sum, flags_group.(cf := new_carry))  }

function addm256(x:Bignum, y:Bignum, mod:Bignum) : Bignum
{ var (sum, new_carry) := BignumAddCarry(x, y, false, 0, false); if sum >= mod then sum - mod else sum }

function sub256(x:Bignum, y:Bignum, st:bool, sb:uint32, flags_group:FlagsGroup) : (Bignum, FlagsGroup)
	requires sb < 32;
{ var (sum, new_carry) := BignumAddCarry(x, -y, st, sb, cf(flags_group)); (sum, flags_group.(cf := new_carry))  }

function mulqacc256(x:Bignum, qx:int, y:Bignum, qy:int, shift:int, zero:bool, wacc:Bignum) : Bignum
	requires 0 <= shift <= 3;
	requires 0 <= qx <= 3;
	requires 0 <= qy <= 3;
{ var result := LeftShift256(GetQuarterWord(x, qx) * GetQuarterWord(y, qy), shift * 64); if zero then result else wacc + result }
	
function xor256(x:Bignum, y:Bignum, st:bool, sb:uint32) : Bignum
	requires sb < 32;
		{ BignumXor(x, y, st, sb) }

function or256(x:Bignum, y:Bignum, st:bool, sb:uint32) : Bignum
	requires sb < 32;
		{ BignumOr(x, y, st, sb) }
		
function and256(x:Bignum, y:Bignum, st:bool, sb:uint32) : Bignum
	requires sb < 32;
		{ BignumAnd(x, y, st, sb) }
}
