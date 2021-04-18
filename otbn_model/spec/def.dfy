include "types.dfy"
include "ops.dfy"
include "../lib/powers.dfy"

module bignum_def {

import opened types
import opened ops    
import opened powers

type reg_index = i: int | 0 <= i < 32

datatype reg32_t = GPR(index: reg_index)

datatype reg256_t =
    | WDR(index: reg_index)
    | WMOD // Wide modulo register
    | WRND // Wide random number
    | WACC // Wide accumulator

datatype ins32 =
    | ADD(xrd: reg32_t, xrs1: reg32_t, xrs2: reg32_t)
    | ADDI(xrd: reg32_t, xrs1: reg32_t, imm: uint32)
    | LUI(xrd: reg32_t, imm: uint32)
    | SUB(xrd: reg32_t, xrs1: reg32_t, xrs2: reg32_t)
    | AND(xrd: reg32_t, xrs1: reg32_t, xrs2: reg32_t)
    | ANDI(xrd: reg32_t, xrs1: reg32_t, imm: uint32)
    | OR(xrd: reg32_t, xrs1: reg32_t, xrs2: reg32_t)
    | ORI(xrd: reg32_t, xrs1: reg32_t, imm: uint32)
    | XOR(xrd: reg32_t, xrs1: reg32_t, xrs2: reg32_t)
    | XORI(xrd: reg32_t, xrs1: reg32_t, imm: uint32)
    | LW(xrd: reg32_t, xrs1: reg32_t, imm: uint32)
    | SW(xrs1: reg32_t, xrs2: reg32_t, imm: uint32)
    | BEQ(xrs1: reg32_t, xrs2: reg32_t, offset: uint32)
    | BNE(xrs1: reg32_t, xrs2: reg32_t, offset: uint32)
    | LOOP(grs: reg32_t, bodysize: uint32)
    | LOOPI(iterations: uint32, bodysize: uint32)
    | JAL(xrd: reg32_t, offset: uint32)
    | JALR(xrd: reg32_t, xrs1: reg32_t, offset: uint32)
    | CSRRS(xrd: reg32_t, csr: reg32_t, xrs2: reg32_t)
    | CSRRW(xrd: reg32_t, csr: reg32_t, xrs2: reg32_t)
    | ECALL // TODO

datatype ins256 =
    | BN_ADD(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift_type: bool, shift_bytes: uint32, fg: uint1)
    | BN_ADDC(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift_type: bool, shift_bytes: uint32, fg: uint1)
    | BN_ADDI(wrd: reg256_t, wrs1: reg256_t, imm: uint256, fg: uint1)
    | BN_ADDM(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t)
    | BN_MULQACC(zero: bool, wrs1: reg256_t, qwsel1: uint32, wrs2: reg256_t, qwsel2: uint32, shift: uint32)
    | BN_MULH(wrd: reg256_t, wrs1: reg256_t, hw1: bool, wrs2: reg256_t, hw2: bool)
    | BN_SUB(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift_type: bool, shift_bytes: uint32, fg: uint1)
    | BN_SUBB(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift_type: bool, shift_bytes: uint32, fg: uint1)
    | BN_SUBI(wrd: reg256_t, wrs1: reg256_t, imm: uint256, fg: uint1)
    | BN_SUBM(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t)
    | BN_AND(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift_type: bool, shift_bytes: uint32)
    | BN_OR(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift_type: bool, shift_bytes: uint32)
    | BN_NOT(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift_type: bool, shift_bytes: uint32)
    | BN_XOR(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, shift_type: bool, shift_bytes: uint32)
    | BN_RSHI(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, imm: uint256)
    | BN_SEL(wrd: reg256_t, wrs1: reg256_t, wrs2: reg256_t, fg: uint1)
    | BN_CMP(wrs1: reg256_t, wrs2: reg256_t, fg: uint1)
    | BN_CMPB(wrs1: reg256_t, wrs2: reg256_t, fg: uint1)
    | BN_LID(grd: reg32_t, grd_inc: bool, offset: uint32, grs: reg32_t, grs_inc: bool)
    | BN_SID(grs2: reg32_t, grs2_inc: bool, offset: uint32, grs1: reg32_t, grs1_inc: bool)
    | BN_MOV(wrd: reg256_t, wrs: reg256_t)
    | BN_MOVR(grd: reg32_t, grd_inc: bool, grs: reg32_t, grs_inc: bool)
    | BN_WSRRS // TODO
    | BN_WSRRW // TODO

datatype code =
    | Ins32(ins: ins32)
    | Ins256(bn_ins: ins256)
    | Block(block: codes)
    | While(whileCond: whileCond, whileBody: code)

datatype codes = CNil | va_CCons(hd: code, tl: codes)

datatype whileCond = 
    | RegCond(r: reg32_t)
    | ImmCond(c: uint32)

// datatype flag = CF | MSB | LSB | ZERO
datatype flags_t = flags_t(cf: bool, msb: bool, lsb: bool, zero: bool)
datatype fgroups_t = fgroups_t(fg0: flags_t, fg1: flags_t)

type gprs_t = gprs : seq<uint32> | |gprs| == 32 witness *
type wdrs_t = wdrs : seq<uint256> | |wdrs| == 32 witness *

datatype state = state(
    gprs: gprs_t,  // 32-bit registers
    wdrs: wdrs_t, // 256-bit registers

    wmod: uint256,
    wrnd: uint256,
    wacc: uint256,

    fgroups: fgroups_t,

    xmem: map<int, uint32>,
    wmem: map<int, uint256>,

    ok: bool)

predicate valid_state(s: state)
{
    s.ok
}

function {:opaque} wmem_seq_core(wmem: map<int, uint256>, start: nat, count: nat): (s: seq<uint256>)
    requires count <= 12 // to prevent use of count as an address
    requires forall i | 0 <= i < count :: valid_wmem_addr(wmem, start + 32 * i)
    ensures |s| == count
    ensures forall i | 0 <= i < |s| :: s[i] == wmem[start + 32 * i];
    decreases count
{
    if count == 0 then []
    else wmem_seq_core(wmem, start, count - 1) + [wmem[start + 32 * (count - 1)]]
}

function wmem_seq(wmem: map<int, uint256>, start: nat, count: nat): (s: seq<uint256>)
    requires count <= 12 // to prevent use of count as an address
    requires forall i | 0 <= i < count :: valid_wmem_addr(wmem, start + 32 * i)
    ensures |s| == count
    ensures forall i | 0 <= i < |s| :: s[i] == wmem[start + 32 * i];
    ensures count > 0 ==> wmem_seq_core(wmem, start, count - 1) + [wmem[start + 32 * (count-1)]] == wmem_seq_core(wmem, start, count)
    decreases count
{
    wmem_seq_core(wmem, start, count) 
}

function wdrs_seq(wdrs: wdrs_t, start: reg_index, end: reg_index): (s: seq<uint256>)
    requires start <= end
    ensures |s| == end - start
{
    wdrs[start..end]
}

function sub_seq<T>(s: seq<T>, start: int, end: int): seq<T>
    requires 0 <= start <= end <= |s|
{
    s[start..end]
}

function seq_empty<T>(): seq<T>
{
    []
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

lemma lemma_extend_seq_subb(
        x: seq<uint256>, y: seq<uint256>, z: seq<uint256>, 
        cin_old:uint1, cin:uint1,
        new_x:uint256, new_y:uint256, new_z:uint256)
    requires |x| == |y|
    requires (z, cin_old) == seq_subb(x, y)
    requires (new_z, cin) == uint256_subb(new_x, new_y, cin_old)
    ensures (z + [new_z], cin) == seq_subb(x + [new_x], y + [new_y])
{
}

lemma lemma_empty_seq_subb()
    ensures ([], 0) == seq_subb([], [])
{
}

predicate valid_xmem_addr(h: map<int, uint32>, addr:int)
{
    addr in h
}

predicate valid_wmem_addr(h: map<int, uint256>, addr:int)
{
    addr in h
}

function eval_reg32(s: state, r: reg32_t) : uint32
{
    s.gprs[r.index]
}

predicate evalIns32(xins: ins32, s: state, r: state)
{
    if !s.ok then
        !r.ok
    else
        r.ok && (valid_state(s) ==> valid_state(r))
}

function eval_reg256(s: state, r: reg256_t) : uint256
{
    match r {
        case WDR(index) => s.wdrs[r.index]
        case WMOD => s.wmod
        case WRND => s.wrnd
        case WACC => s.wacc
    }
}

predicate eval_ins256(wins: ins256, s: state, r: state)
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
{
    match wc 
        case RegCond(r) => eval_reg32(s, r)
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
        case Ins256(ins) => eval_ins256(ins, s, r)
        case Block(block) => evalBlock(block, s, r)
        //case IfElse(cond, ifT, ifF) => evalIfElse(cond, ifT, ifF, s, r)
        case While(cond, body) => evalWhile(body, eval_cond(s, cond), s, r)
}

function select_fgroup(fgps: fgroups_t, which: uint1): flags_t
{
    if which == 0 then fgps.fg0 else fgps.fg1
}

function get_flag(fgps: fgroups_t, which_group: uint1, which_flag: int) : bool
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

function get_cf0(fgps: fgroups_t): bool
{
    select_fgroup(fgps, 0).cf 
}

function get_cf1(fgps: fgroups_t): bool
{
    select_fgroup(fgps, 1).cf 
}

function update_fgroups(fgps: fgroups_t, which_group: uint1, new_flags_t: flags_t) : fgroups_t
{
    if which_group == 0 then fgps.(fg0 := new_flags_t) else fgps.(fg1 := new_flags_t)
}

function otbn_add_carray(a: uint256, b: uint256, carry_in: bool) : (uint256, flags_t)
{
    var sum : int := a + b + if carry_in then 1 else 0;
    // FIXME: get MSB and LSM
    var fg := flags_t(sum / BASE_256 != 0, false, false, sum == 0);
    (sum % BASE_256, fg)
}

function otbn_add(x: uint256, y: uint256, st: bool, sb: uint32) : (uint256, flags_t)
    requires sb < 32;
{
    otbn_add_carray(x, uint256_sb(y, st, sb), false)
}

function otbn_addc(x: uint256, y: uint256, st: bool, sb: uint32, fg: flags_t) : (uint256, flags_t)
    requires sb < 32;
{
    otbn_add_carray(x, uint256_sb(y, st, sb), fg.cf)
}

function otbn_addi(x: uint256, imm: uint256) : (uint256, flags_t)
    requires imm < 1024;
{
    otbn_add_carray(x, imm, false)
}

function otbn_addm(x: uint256, y: uint256, mod: uint256) : uint256
{
    var (sum, _) := otbn_add_carray(x, y, false);
    if sum >= mod then sum - mod else sum
}

function otbn_sub(x: uint256, y: uint256, st: bool, sb: uint32) : (uint256, flags_t)
    requires sb < 32;
{
    var diff : int := x - uint256_sb(y, st, sb);
    // FIXME: figure out the flags_t
    var fg := flags_t(false, false, false, diff == 0);
    (diff % BASE_256, fg)
}

function otbn_subb(x: uint256, y: uint256, st: bool, sb : uint32, flgs: flags_t) : (uint256, flags_t)
    requires sb < 32;
{
    var cf := if flgs.cf then 1 else 0;
	var (diff, cout) := uint256_subb(x, uint256_sb(y, st, sb), cf);
    var fg := flags_t(cout == 1, false, false, diff == 0);
    (diff, fg)
}

function otbn_subbi(x: uint256, imm: uint256) : (uint256, flags_t)
    requires imm < 1024;
    // requires imm < x; //TODO: Is this true?
{
    // FIXME: double check this
    var diff : int := x - imm;
    // FIXME: figure out the flags_t
    var fg := flags_t(false, false, false, diff == 0);
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
