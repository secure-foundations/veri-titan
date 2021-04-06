include "types.dfy"
include "ops.dfy"
include "../lib/powers.dfy"

module bignum_def {

import opened types
import opened ops    
import opened powers

type reg_index = i: int | 0 <= i < 32

// General purpose and control registers, 32b
datatype Reg32 =
| Gpr(x: reg_index)
| Rnd // Random number

// Wide data and special registers, 256b
datatype Reg256 =
| Wdr(w: reg_index)
| WMod // Wide modulo register
| WRnd // Wide random number
| WAcc // Wide accumulator

datatype ins32 =
| ADD(xrd: Reg32, xrs1: Reg32, xrs2: Reg32)
| ADDI(xrd: Reg32, xrs1: Reg32, imm: uint32)
| LUI(xrd: Reg32, imm: uint32)
| SUB(xrd: Reg32, xrs1: Reg32, xrs2: Reg32)
| AND(xrd: Reg32, xrs1: Reg32, xrs2: Reg32)
| ANDI(xrd: Reg32, xrs1: Reg32, imm: uint32)
| OR(xrd: Reg32, xrs1: Reg32, xrs2: Reg32)
| ORI(xrd: Reg32, xrs1: Reg32, imm: uint32)
| XOR(xrd: Reg32, xrs1: Reg32, xrs2: Reg32)
| XORI(xrd: Reg32, xrs1: Reg32, imm: uint32)
| LW(xrd: Reg32, xrs1: Reg32, imm: uint32)
| SW(xrs1: Reg32, xrs2: Reg32, imm: uint32)
| BEQ(xrs1: Reg32, xrs2: Reg32, offset: uint32)
| BNE(xrs1: Reg32, xrs2: Reg32, offset: uint32)
| LOOP(grs: Reg32, bodysize: uint32)
| LOOPI(iterations: uint32, bodysize: uint32)
| JAL(xrd: Reg32, offset: uint32)
| JALR(xrd: Reg32, xrs1: Reg32, offset: uint32)
| CSRRS(xrd: Reg32, csr: Reg32, xrs2: Reg32)
| CSRRW(xrd: Reg32, csr: Reg32, xrs2: Reg32)
| ECALL // TODO

datatype ins256 =
| BN_ADD(wrd: Reg256, wrs1: Reg256, wrs2: Reg256, shift_type: bool, shift_bytes: uint32, fg: uint1)
| BN_ADDC(wrd: Reg256, wrs1: Reg256, wrs2: Reg256, shift_type: bool, shift_bytes: uint32, fg: uint1)
| BN_ADDI(wrd: Reg256, wrs1: Reg256, imm: uint256, fg: uint1)
| BN_ADDM(wrd: Reg256, wrs1: Reg256, wrs2: Reg256)
| BN_MULQACC(zero: bool, wrs1: Reg256, qwsel1: uint32, wrs2: Reg256, qwsel2: uint32, shift: uint32)
| BN_MULH(wrd: Reg256, wrs1: Reg256, hw1: bool, wrs2: Reg256, hw2: bool)
| BN_SUB(wrd: Reg256, wrs1: Reg256, wrs2: Reg256, shift_type: bool, shift_bytes: uint32, fg: uint1)
| BN_SUBB(wrd: Reg256, wrs1: Reg256, wrs2: Reg256, shift_type: bool, shift_bytes: uint32, fg: uint1)
| BN_SUBI(wrd: Reg256, wrs1: Reg256, imm: uint256, fg: uint1)
| BN_SUBM(wrd: Reg256, wrs1: Reg256, wrs2: Reg256)
| BN_AND(wrd: Reg256, wrs1: Reg256, wrs2: Reg256, shift_type: bool, shift_bytes: uint32)
| BN_OR(wrd: Reg256, wrs1: Reg256, wrs2: Reg256, shift_type: bool, shift_bytes: uint32)
| BN_NOT(wrd: Reg256, wrs1: Reg256, wrs2: Reg256, shift_type: bool, shift_bytes: uint32)
| BN_XOR(wrd: Reg256, wrs1: Reg256, wrs2: Reg256, shift_type: bool, shift_bytes: uint32)
| BN_RSHI(wrd: Reg256, wrs1: Reg256, wrs2: Reg256, imm: uint256)
| BN_SEL(wrd: Reg256, wrs1: Reg256, wrs2: Reg256, fg: uint1)
| BN_CMP(wrs1: Reg256, wrs2: Reg256, fg: uint1)
| BN_CMPB(wrs1: Reg256, wrs2: Reg256, fg: uint1)
| BN_LID(grd: Reg32, grd_inc: bool, offset: uint32, grs: Reg32, grs_inc: bool)
| BN_SID(grs2: Reg32, grs2_inc: bool, offset: uint32, grs1: Reg32, grs1_inc: bool)
| BN_MOV(wrd: Reg256, wrs: Reg256)
| BN_MOVR(grd: Reg32, grd_inc: bool, grs: Reg32, grs_inc: bool)
| BN_WSRRS // TODO
| BN_WSRRW // TODO

datatype code =
| Ins32(ins: ins32)
| Ins256(bn_ins: ins256)
| Block(block: codes)
| While(whileCond: whileCond, whileBody: code)

datatype codes = CNil | va_CCons(hd: code, tl: codes)

datatype whileCond = 
    | RegCond(r: Reg32)
    | ImmCond(c: uint32)

// datatype flag = CF | MSB | LSB | ZERO
datatype flags = flags(cf: bool, msb: bool, lsb: bool, zero: bool)
datatype flagGroups = flagGroups(fg0: flags, fg1: flags)

datatype state = state(
    xregs: map<Reg32, uint32>, // 32-bit registers
    wregs: map<Reg256, uint256>, // 256-bit registers
    fgroups: flagGroups,
    xmem: map<int, uint32>,
    wmem: map<int, uint256>,
    ok: bool)

predicate valid_state(s: state)
{
    && (forall r :: r in s.xregs)
    && (forall t :: t in s.wregs)
}

function wregs_seq_rev(wregs: map<Reg256, uint256>, start: reg_index, end: reg_index): seq<uint256>
    requires forall t :: t in wregs
    requires start <= end
    decreases end - start
{
    if start == end then []
    else [wregs[Wdr(start)]] + wregs_seq(wregs, start + 1, end)
}

function wregs_seq(wregs: map<Reg256, uint256>, start: reg_index, end: reg_index): (s: seq<uint256>)
    requires forall t :: t in wregs
    requires start <= end
    ensures |s| == end - start
    ensures forall i | 0 <= i < |s| :: s[i] == wregs[Wdr(i + start)];
    decreases end - start
{
    if start == end then []
    else 
    var partial := wregs_seq(wregs, start, end - 1);
    var s := partial + [wregs[Wdr(end-1)]];
    s    
}

lemma wregs_seq_contents(wregs: map<Reg256, uint256>, start: reg_index, end: reg_index, s: seq<uint256>)
    requires forall t :: t in wregs
    requires start <= end
    requires s == wregs_seq(wregs, start, end)
    ensures forall i | 0 <= i < |s| :: s[i] == wregs[Wdr(i + start)];
{
    if start != end {
        var partial := wregs_seq(wregs, start, end - 1);
        var s := partial + [wregs[Wdr(end-1)]];
        forall i | 0 <= i < |s| ensures s[i] == wregs[Wdr(i + start)] {
            if i < |s| - 1 {
                wregs_seq_contents(wregs, start, end - 1, partial);
                assert s[i] == partial[i];
            } else {
                assert s[i] == wregs[Wdr(i + start)];
            }
        }
    }
}

// lemma test(wregs: map<Reg256, uint256>)
//     requires forall t :: t in wregs
// {
//     var s := wregs_seq(wregs, 3, 12);
//     var wregs' := wregs[Wdr(13) := 42];
//     var s' := wregs_seq(wregs', 3, 12);
//     assert s' == s[8 := 42];
// }

function wmem_seq(wmem: map<int, uint256>, start: nat, count: nat): (s: seq<uint256>)
    requires count <= 12 // to prevent use of count as an address
    requires forall i | 0 <= i < count :: Valid256Addr(wmem, start + 32 * i)
    ensures |s| == count
    ensures forall i | 0 <= i < |s| :: s[i] == wmem[start + 32 * i];
    decreases count
{
    if count == 0 then []
    else wmem_seq(wmem, start, count - 1) + [wmem[start + 32 * (count - 1)]]
}

// function wdr_seq(wregs: map<Reg256, uint256>, start: reg_index, end: reg_index): int 
//     requires start <= end
//     decreases end - start
//     fix domain
// {
//     if start == end then wregs[Wdr(start)]
//     else BASE_256 * interp_wdr_seq(wregs, start + 1, end) + wregs[Wdr(start)]
// }

function fst<T,Q>(t:(T, Q)) : T { t.0 }
function snd<T,Q>(t:(T, Q)) : Q { t.1 }

function sub_seq<T>(s: seq<T>, start: int, end: int): seq<T>
    requires 0 <= start <= end <= |s|
{
    s[start..end]
}

function prefix_seq<T>(s: seq<T>, end: int): seq<T>
    requires 0 <= end <= |s|
{
    s[..end]
}

function seq_len<T>(s: seq<T>): nat
{
    |s|
}

function seq_concat<T>(x: seq<T>, y: seq<T>): seq<T>
{
    x + y
}

function seq_append<T>(xs: seq<T>, x: T): seq<T>
{
    xs + [x]
}

function seq_subb(x: seq<uint256>, y: seq<uint256>) : (seq<uint256>, uint1)
    requires |x| == |y|
    ensures var (z, cout) := seq_subb(x, y);
        && |z| == |x|
{
    if |x| == 0 then ([], 0)
    else 
        var idx := |x| - 1;
        var (zrest, ctmp) := seq_subb(prefix_seq(x, idx), prefix_seq(y, idx));
        var (z0, cout) := uint256_subb(x[idx], y[idx], ctmp);
        (zrest + [z0], cout)
}

// function seq_subb(x: seq<uint256>, y: seq<uint256>, cin: uint1) : (seq<uint256>, uint1)
//     requires |x| == |y|
//     ensures var (z, cout) := seq_subb(x, y, cin);
//         && |z| == |x|
// {
//     if |x| == 0 then ([], cin)
//     else 
//         var (z0, c) := uint256_subb(x[0], y[0], cin);
//         var (zrest, cout) := seq_subb(x[1..], y[1..], c);
//         ([z0] + zrest, cout)
// }

predicate Valid32Addr(h: map<int, uint32>, addr:int)
{
    addr in h
}

predicate Valid256Addr(h: map<int, uint256>, addr:int)
{
    addr in h
}

predicate IsUInt32(i: int) { 0 <= i < 0x1_0000_0000 }

predicate IsUInt256(i: int) { 0 <= i < 0x1_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000 }

predicate ValidRegister32(xregs: map<Reg32, uint32>, r: Reg32)
{
    r in xregs
}

predicate ValidRegister256(wregs: map<Reg256, uint256>, r: Reg256)
{
    r in wregs
}

predicate ValidCsr32(r: Reg32)
{
    // TODO: Other CSRs are limbs of WMod or flags-- will these ever be used?
    r.Rnd?
}

function eval_xreg(xregs: map<Reg32, uint32>, r: Reg32) : uint32
{
    if !ValidRegister32(xregs, r) then 24 // TODO: better error message
    else xregs[r]
}

function eval_wreg(wregs: map<Reg256, uint256>, r: Reg256) : uint256
{
    if !ValidRegister256(wregs, r) then 24 // TODO: better error message
    else wregs[r]
}

predicate ValidSourceRegister32(s: state, r: Reg32)
{
    ValidRegister32(s.xregs, r)
}

predicate ValidDestinationRegister32(s: state, r: Reg32)
{
    !r.Rnd? && ValidRegister32(s.xregs, r)
}

function eval_reg32(s: state, r: Reg32) : uint32
{
    if !ValidSourceRegister32(s, r) then
        42
    else
        s.xregs[r]
}

predicate evalIns32(xins: ins32, s: state, r: state)
{
    if !s.ok then
        !r.ok
    else
        r.ok && (valid_state(s) ==> valid_state(r))
}

predicate ValidSourceRegister256(s: state, r: Reg256)
{
    ValidRegister256(s.wregs, r)
}

predicate ValidDestinationRegister256(s: state, r: Reg256)
{
    !r.WRnd? && ValidRegister256(s.wregs, r)
}

function eval_reg256(s: state, r: Reg256) : uint256
{
    if !ValidSourceRegister256(s, r) then
        42
    else
        s.wregs[r]
}

predicate evalIns256(wins: ins256, s: state, r: state)
{
    if !s.ok then
        !r.ok
    else
        r.ok && (valid_state(s) ==> valid_state(r))
}

predicate evalBlock(block: codes, s: state, r: state)
{
    if block.CNil? then
        r == s
    else
        exists r': state :: evalCode(block.hd, s, r') && evalBlock(block.tl, r', r)
}

function eval_cond(s: state, wc: whileCond): nat
    // requires ValidSourceRegister32(s, wc.r);
    // requires IsUInt32(wc.c);
{
    match wc 
        case RegCond(r) => eval_xreg(s.xregs, r)
        case ImmCond(c) => c
}

predicate evalWhile(c: code, n: nat, s: state, r: state)
    decreases c, n
{
    if s.ok then
        if n == 0 then
            s == r
        else
            exists loop_body_end: state :: evalCode(c, s, loop_body_end)
                && evalWhile(c, n - 1, loop_body_end, r)
    else
        !r.ok
}

predicate evalCode(c: code, s: state, r: state)
    decreases c, 0
{
    match c
        case Ins32(ins) => evalIns32(ins, s, r)
        case Ins256(ins) => evalIns256(ins, s, r)
        case Block(block) => evalBlock(block, s, r)
        //case IfElse(cond, ifT, ifF) => evalIfElse(cond, ifT, ifF, s, r)
        case While(cond, body) => evalWhile(body, eval_cond(s, cond), s, r)
}

function select_fgroup(fgps: flagGroups, which: uint1): flags
{
    if which == 0 then fgps.fg0 else fgps.fg1
}

function get_flag(fgps: flagGroups, which_group: uint1, which_flag: int) : bool
    requires 0 <= which_flag <= 3;
{
    if which_flag == 0 then select_fgroup(fgps, which_group).cf 
    else if which_flag == 1 then select_fgroup(fgps, which_group).msb
    else if which_flag == 2 then select_fgroup(fgps, which_group).lsb
    else select_fgroup(fgps, which_group).zero
}

function bool_to_uint1(i:bool) : uint1
{
    if i then 1 else 0
}

function get_cf0(fgps: flagGroups): bool
{
    select_fgroup(fgps, 0).cf 
}

function get_cf1(fgps: flagGroups): bool
{
    select_fgroup(fgps, 1).cf 
}

function update_fgroups(fgps: flagGroups, which_group: uint1, new_flags: flags) : flagGroups
{
    if which_group == 0 then fgps.(fg0 := new_flags) else fgps.(fg1 := new_flags)
}

function otbn_add_carray(a: uint256, b: uint256, carry_in: bool) : (uint256, flags)
{
    var sum : int := a + b + if carry_in then 1 else 0;
    // FIXME: get MSB and LSM
    var fg := flags(sum / BASE_256 != 0, false, false, sum == 0);
    (sum % BASE_256, fg)
}

function otbn_add(x: uint256, y: uint256, st: bool, sb: uint32) : (uint256, flags)
    requires sb < 32;
{
    otbn_add_carray(x, uint256_sb(y, st, sb), false)
}

function otbn_addc(x: uint256, y: uint256, st: bool, sb: uint32, fg: flags) : (uint256, flags)
    requires sb < 32;
{
    otbn_add_carray(x, uint256_sb(y, st, sb), fg.cf)
}

function otbn_addi(x: uint256, imm: uint256) : (uint256, flags)
    requires imm < 1024;
{
    otbn_add_carray(x, imm, false)
}

function otbn_addm(x: uint256, y: uint256, mod: uint256) : uint256
{
    var (sum, _) := otbn_add_carray(x, y, false);
    if sum >= mod then sum - mod else sum
}

function otbn_sub(x: uint256, y: uint256, st: bool, sb: uint32) : (uint256, flags)
    requires sb < 32;
{
    var diff : int := x - uint256_sb(y, st, sb);
    // FIXME: figure out the flags
    var fg := flags(false, false, false, diff == 0);
    (diff % BASE_256, fg)
}

function otbn_subb(x: uint256, y: uint256, st: bool, sb : uint32, flgs: flags) : (uint256, flags)
    requires sb < 32;
{
    // TODO: replace this with uint256_subb
    var cf := if flgs.cf then 1 else 0;
	var (diff, cout) := uint256_subb(x, uint256_sb(y, st, sb), cf);
    var fg := flags(cout == 1, false, false, diff == 0);
    (diff, fg)
}

function otbn_subbi(x: uint256, imm: uint256) : (uint256, flags)
    requires imm < 1024;
    // requires imm < x; //TODO: Is this true?
{
    // FIXME: double check this
    var diff : int := x - imm;
    // FIXME: figure out the flags
    var fg := flags(false, false, false, diff == 0);
    (diff % BASE_256, fg)
}

function otbn_subm(x: uint256, y: uint256, wmod: uint256) : uint256
{
    // FIXME: some bound checking?
    assume false;
    var result := (x as bv256 - y as bv256) as uint256;
    if result >= wmod then (result as bv256 - wmod as bv256) as uint256 else result
}

function otbn_mulqacc(
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

predicate otbn_mulqacc_is_safe(shift: uint2, acc: uint256)
{
    // make sure no overflow from shift (product is assumed to be 128 bits)
    && (shift <= 2) 
    // make sure no overflow from addtion
    && (acc + otbn_qshift_safe(BASE_128 - 1, shift) < BASE_256)
}

// mulquacc but no overflow
function otbn_mulqacc_safe(
    zero: bool,
    x: uint256, qx: uint2,
    y: uint256, qy: uint2,
    shift: uint2,
    acc: uint256) : uint256

    requires otbn_mulqacc_is_safe(shift, acc);
{
    var product := uint256_qmul(x, qx, y, qy);
    var shift := otbn_qshift_safe(product, shift);
    if zero then shift else acc + shift
}

// quater shift but no overflow
function otbn_qshift_safe(x: uint256, q: uint2): (r: uint256)
    requires (q == 1) ==> (x < BASE_192);
    requires (q == 2) ==> (x < BASE_128);
    requires (q == 3) ==> (x < BASE_64);
{
    if q == 0 then x
    else if q == 1 then x * BASE_64
    else if q == 2 then x * BASE_128
    else x * BASE_192
}

function otbn_xor(x: uint256, y: uint256, st: bool, sb: uint32) : uint256
    requires sb < 32;
{
    uint256_xor(x, uint256_sb(y, st, sb))
}

function otbn_or(x: uint256, y: uint256, st: bool, sb: uint32) : uint256
    requires sb < 32;
{
    uint256_or(x, uint256_sb(y, st, sb))
}
        
function otbn_and(x: uint256, y: uint256, st: bool, sb: uint32) : uint256
    requires sb < 32;
{
    uint256_and(x, uint256_sb(y, st, sb))
}

function otbn_rshi(x: uint256, y: uint256, shift_amt: int) : uint256
    requires 0 <= shift_amt < 256;
{
    var concat : int := x * BASE_256 + y;
    (concat / pow2(shift_amt)) % BASE_256
}

}