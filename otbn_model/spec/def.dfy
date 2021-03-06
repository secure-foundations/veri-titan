include "types.dfy"
include "ops.dfy"
include "../lib/powers.dfy"

module bignum_def {

import opened types
import opened ops    
import opened powers

type reg_index = i:int | 0 <= i < 32

// General purpose and control registers, 32b
datatype Reg32 =
| Gpr(x:reg_index)
| Rnd // Random number

// Wide data and special registers, 256b
datatype Reg256 =
| Wdr(w:reg_index)
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
| LW32(xrd:Reg32, xrs1:Reg32, imm:uint32)
| SW32(xrs1:Reg32, xrs2:Reg32, imm:uint32)
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
| ADDI256(wrd:Reg256, wrs1:Reg256, imm: uint256, flg:bool)
| ADDM256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256)
| MULQACC256(zero:bool, wrs1:Reg256, qwsel1:uint32, wrs2:Reg256, qwsel2:uint32, shift:uint32)
| MULH256(wrd:Reg256, wrs1:Reg256, hw1:bool, wrs2:Reg256, hw2:bool)
| SUB256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint32, flg:bool)
| SUBB256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint32, flg:bool)
| SUBI256(wrd:Reg256, wrs1:Reg256, imm: uint256, flg:bool)
| SUBM256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256)
| AND256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint32)
| OR256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint32)
| NOT256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint32)
| XOR256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, shift_type:bool, shift_bytes:uint32)
| RSHI256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, imm: uint256)
| SEL256(wrd:Reg256, wrs1:Reg256, wrs2:Reg256, flg:bool)
| CMP256(wrs1:Reg256, wrs2:Reg256, flg:bool)
| CMPB256(wrs1:Reg256, wrs2:Reg256, flg:bool)
// BN.LID <grd>[<grd_inc>], <offset>(<grs1>[<grs1_inc>])
| LID256(grd:Reg32, grd_inc:bool, offset:uint32, grs:Reg32, grs_inc:bool)
// BN.SID <grs2>[<grs2_inc>], <offset>(<grs1>[<grs1_inc>])
| SID256(grs2:Reg32, grs2_inc:bool, offset:uint32, grs1:Reg32, grs1_inc:bool)
| MOV256(wrd:Reg256, wrs:Reg256)
| MOVR256 // TODO
| WSRRS256 // TODO
| WSRRW256 // TODO

datatype code =
| Ins32(ins:ins32)
| Ins256(bn_ins:ins256)
| Block(block:codes)
| While(whileCond:whileCond, whileBody:code)

datatype codes = CNil | va_CCons(hd:code, tl:codes)

datatype cmp = Eq | Ne | Gt | Ge | Lt | Le
datatype whileCond = 
    | RegCond(r: Reg32)
    | ImmCond(c: uint32)

datatype FlagsGroup = FlagsGroup(cf:bool, msb:bool, lsb:bool, zero:bool)
datatype Flags = Flags(fg0:FlagsGroup, fg1:FlagsGroup)

datatype mAddr = mAddr(reg:Reg32, offset:int)

datatype state = state(
    xregs: map<Reg32, uint32>, // 32-bit registers
    wregs: map<Reg256, uint256>, // 256-bit registers
    flags: Flags,
    // lstack: seq<nat>,
    xmem: map<int, uint32>,
    wmem: map<int, uint256>,
    ok: bool)

predicate valid_state(s:state)
{
    && (forall r :: r in s.xregs)
    && (forall t :: t in s.wregs)
}

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

predicate ValidSourceRegister32(s:state, r:Reg32)
{
    ValidRegister32(s.xregs, r)
}

predicate ValidDestinationRegister32(s:state, r:Reg32)
{
    !r.Rnd? && ValidRegister32(s.xregs, r)
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
    if !s.ok then
        !r.ok
    else
        r.ok && (valid_state(s) ==> valid_state(r))
}

predicate ValidSourceRegister256(s:state, r:Reg256)
{
    ValidRegister256(s.wregs, r)
}

predicate ValidDestinationRegister256(s:state, r:Reg256)
{
    !r.WRnd? && ValidRegister256(s.wregs, r)
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
        r.ok && (valid_state(s) ==> valid_state(r))
}

predicate evalBlock(block:codes, s:state, r:state)
{
    if block.CNil? then
        r == s
    else
        exists r':state :: evalCode(block.hd, s, r') && evalBlock(block.tl, r', r)
}

// function evalCmp(c:cmp, i1:uint32, i2:uint32):bool
// {
//     match c
//         case Eq => i1 == i2
//         case Ne => i1 != i2
//         case Gt => i1 > i2
//         case Ge => i1 >= i2
//         case Lt => i1 < i2
//         case Le => i1 <= i2
// }

function eval_cond(s:state, wc:whileCond): nat
    // requires ValidSourceRegister32(s, wc.r);
    // requires IsUInt32(wc.c);
{
    match wc 
        case RegCond(r) => eval_xreg(s.xregs, r)
        case ImmCond(c) => c
}

predicate evalWhile(c:code, n:nat, s:state, r:state)
    decreases c, n
{
    if s.ok then
        if n == 0 then
            s == r
        else
            exists loop_body_end:state :: evalCode(c, s, loop_body_end)
                && evalWhile(c, n - 1, loop_body_end, r)
    else
        !r.ok
}

predicate evalCode(c:code, s:state, r:state)
    decreases c, 0
{
    match c
        case Ins32(ins) => evalIns32(ins, s, r)
        case Ins256(ins) => evalIns256(ins, s, r)
        case Block(block) => evalBlock(block, s, r)
        //case IfElse(cond, ifT, ifF) => evalIfElse(cond, ifT, ifF, s, r)
        case While(cond, body) => evalWhile(body, eval_cond(s, cond), s, r)
}

function get_flags_group(fg:bool, flags:Flags) : FlagsGroup { if fg then flags.fg1 else flags.fg0 }

function get_flag(fg:bool, flag:int, flags:Flags) : bool
    requires 0 <= flag <= 4;
{
    if flag == 0 then get_flags_group(fg, flags).cf else
    if flag == 1 then get_flags_group(fg, flags).msb else
    if flag == 2 then get_flags_group(fg, flags).lsb else
    get_flags_group(fg, flags).zero
}

function update_fg(b:bool, f:Flags, fg:FlagsGroup) : Flags { if b then f.(fg1 := fg) else f.(fg0 := fg) }

function cf(flags_group:FlagsGroup) : bool { flags_group.cf }

function bn_add_carray(a: uint256, b: uint256, carry_in: bool) : (uint256, FlagsGroup)
{
    var sum :int := a + b + if carry_in then 1 else 0;
    // FIXME: get MSB and LSM
    var fg := FlagsGroup(sum >= BASE_256, false, false, sum == 0);
    (sum % BASE_256, fg)
}

function bn_add(x: uint256, y: uint256, st: bool, sb: uint32) : (uint256, FlagsGroup)
    requires sb < 32;
{
    bn_add_carray(x, uint256_sb(y, st, sb), false)
}

function bn_addc(x: uint256, y: uint256, st: bool, sb: uint32, flags_group:FlagsGroup) : (uint256, FlagsGroup)
    requires sb < 32;
{
    bn_add_carray(x, uint256_sb(y, st, sb), cf(flags_group))
}

function bn_addi(x: uint256, imm: uint256) : (uint256, FlagsGroup)
    requires imm < 1024;
{
    bn_add_carray(x, imm, false)
}

function bn_addm(x: uint256, y: uint256, mod: uint256) : uint256
{
    var (sum, _) := bn_add_carray(x, y, false);
    if sum >= mod then sum - mod else sum
}

function bn_sub(x: uint256, y: uint256, st: bool, sb: uint32) : (uint256, FlagsGroup)
    requires sb < 32;
{
    var diff :int := x - uint256_sb(y, st, sb);
    // FIXME: figure out the flags
    var fg := FlagsGroup(false, false, false, diff == 0);
    (diff % BASE_256, fg)
}

function bn_subb(x: uint256, y: uint256, st: bool, sb :uint32, flags_group: FlagsGroup) : (uint256, FlagsGroup)
    requires sb < 32;
{
    // FIXME: double check this
    var cf := if cf(flags_group) then 1 else 0;
    var diff :int := x - uint256_sb(y, st, sb) - cf;
    var fg := FlagsGroup(false, false, false, diff == 0);
    (diff % BASE_256, fg)
}

function bn_subbi(x: uint256, imm: uint256) : (uint256, FlagsGroup)
    requires imm < 1024;
    // requires imm < x; //TODO: Is this true?
{
    // FIXME: double check this
    var diff :int := x - imm;
    // FIXME: figure out the flags
    var fg := FlagsGroup(false, false, false, diff == 0);
    (diff % BASE_256, fg)
}

function bn_subm(x: uint256, y: uint256, wmod: uint256) : uint256
{
    // FIXME: some bound checking?
    assume false;
    var result := (x as bv256 - y as bv256) as uint256;
    if result >= wmod then (result as bv256 - wmod as bv256) as uint256 else result
}

function bn_mulqacc(
    zero: bool,
    x: uint256, qx: uint2,
    y: uint256, qy: uint2,
    shift: uint2,
    acc: uint256) : uint256
{
    var product := uint256_qmul(x, qx, y, qy);
    var shift := uint256_ls(product, shift * 8);
    if zero then shift else (acc + shift) % BASE_256
}

predicate bn_mulqacc_is_safe(shift: uint2, acc: uint256)
{
    // make sure no overflow from shift (product is assumed to be 128 bits)
    && (shift <= 2) 
    // make sure no overflow from addtion
    && (acc + bn_qshift_safe(BASE_128 - 1, shift) < BASE_256)
}

// mulquacc but no overflow
function bn_mulqacc_safe(
    zero: bool,
    x: uint256, qx: uint2,
    y: uint256, qy: uint2,
    shift: uint2,
    acc: uint256) : uint256

    requires bn_mulqacc_is_safe(shift, acc);
{
    var product := uint256_qmul(x, qx, y, qy);
    var shift := bn_qshift_safe(product, shift);
    if zero then shift else acc + shift
}

// quater shift but no overflow
function bn_qshift_safe(x: uint256, q: uint2): (r: uint256)
    requires (q == 1) ==> (x < BASE_192);
    requires (q == 2) ==> (x < BASE_128);
    requires (q == 3) ==> (x < BASE_64);
{
    if q == 0 then x
    else if q == 1 then x * BASE_64
    else if q == 2 then x * BASE_128
    else x * BASE_192
}

function bn_xor(x: uint256, y: uint256, st: bool, sb: uint32) : uint256
    requires sb < 32;
{
    uint256_xor(x, uint256_sb(y, st, sb))
}

function bn_or(x: uint256, y: uint256, st: bool, sb: uint32) : uint256
    requires sb < 32;
{
    uint256_or(x, uint256_sb(y, st, sb))
}
        
function bn_and(x: uint256, y: uint256, st: bool, sb: uint32) : uint256
    requires sb < 32;
{
    uint256_and(x, uint256_sb(y, st, sb))
}

function bn_rshi(x: uint256, y: uint256, shift_amt:int) : uint256
    requires 0 <= shift_amt < 256;
{
    var concat : int := x * BASE_256 + y;
    (concat / pow2(shift_amt)) % BASE_256
}

}