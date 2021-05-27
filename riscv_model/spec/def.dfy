include "types.dfy"
include "ops.dfy"
include "../lib/powers.dfy"

module riscv_def {

import opened types
import opened ops
import opened powers

type reg_index = i: int | 0 <= i < 32
datatype Reg32 =
| Gpr(r: reg_index) // 32 32-bit registers, x0 is always zero

// base integer instruction set, 32-bit
datatype ins32I =
| RV_LB(rd: Reg32, rs1: Reg32, oimm12: uint32)
| RV_LH (rd: Reg32, rs1: Reg32, oimm12: uint32)
| RV_LW (rd: Reg32, rs1: Reg32, oimm12: uint32)
| RV_LBU (rd: Reg32, rs1: Reg32, oimm12: uint32)
| RV_LHU (rd: Reg32, rs1: Reg32, oimm12: uint32)

| RV_FENCE (pred: uint32, succ: uint32)
| RV_FENCE_I

| RV_ADDI (rd: Reg32, rs1: Reg32, imm12: uint32) // sign extends, ignore overflow
| RV_SLLI (rd: Reg32, rs1: Reg32, shamt6: uint32) // logical left shift
| RV_SLTI (rd: Reg32, rs1: Reg32, imm12: uint32) // sign extend, 1 if rs1 (signed) < imm, else 0
| RV_SLTIU (rd: Reg32, rs1: Reg32, imm12: uint32) // compare both vals as unsigned.
| RV_XORI (rd: Reg32, rs1: Reg32, imm12: uint32)
| RV_ORI (rd: Reg32, rs1: Reg32, imm12: uint32)
| RV_ANDI (rd: Reg32, rs1: Reg32, imm12: uint32)
| RV_SRLI (rd: Reg32, rs1: Reg32, shamt6: uint32) // logical right shift
| RV_SRAI (rd: Reg32, rs1: Reg32, shamt6: uint32) // arithmetic right shift

| RV_AUIPC (rd: Reg32, oimm20: uint32)

| RV_SB (rs1: Reg32, rs2: Reg32, simm12: uint32)
| RV_SH (rs1: Reg32, rs2: Reg32, simm12: uint32)
| RV_SW (rs1: Reg32, rs2: Reg32, simm12: uint32)

| RV_ADD (rd: Reg32, rs1: Reg32, rs2: Reg32) // ignore overflow
| RV_SUB (rd: Reg32, rs1: Reg32, rs2: Reg32) // ignore overflow
| RV_SLL (rd: Reg32, rs1: Reg32, rs2: Reg32) // shift logical left by "lower 5 bits of rs2"
| RV_SLT (rd: Reg32, rs1: Reg32, rs2: Reg32) // signed less than
| RV_SLTU (rd: Reg32, rs1: Reg32, rs2: Reg32) // unsigned less than
| RV_XOR (rd: Reg32, rs1: Reg32, rs2: Reg32) // bitwise
| RV_SRL (rd: Reg32, rs1: Reg32, rs2: Reg32) // shift logical right by "lower 5 bits of rs2"
| RV_SRA (rd: Reg32, rs1: Reg32, rs2: Reg32) // shift arithmetic right by "lower 5 bits of rs2"
| RV_OR (rd: Reg32, rs1: Reg32, rs2: Reg32) // bitwise
| RV_AND (rd: Reg32, rs1: Reg32, rs2: Reg32) // bitwise

| RV_LUI (rd: Reg32, imm20: uint32)

// | RV_BEQ (rs1: Reg32, rs2: Reg32, sbimm12: uint32)
// | RV_BNE (rs1: Reg32, rs2: Reg32, sbimm12: uint32)
// | RV_BLT (rs1: Reg32, rs2: Reg32, sbimm12: uint32)
// | RV_BGE (rs1: Reg32, rs2: Reg32, sbimm12: uint32)
// | RV_BLTU (rs1: Reg32, rs2: Reg32, sbimm12: uint32)
// | RV_BGEU (rs1: Reg32, rs2: Reg32, sbimm12: uint32)
// 
// | RV_JALR (rd: Reg32, rs1: Reg32, oimm12: uint32)
// | RV_JAL (rd: Reg32, jimm20: uint32)

// standard extension for integer mult and div, 32-bit
datatype ins32M =
| RV_MUL (rd: Reg32, rs1: Reg32, rs2: Reg32)
| RV_MULH (rd: Reg32, rs1: Reg32, rs2: Reg32)
| RV_MULHSU (rd: Reg32, rs1: Reg32, rs2: Reg32)
| RV_MULHU (rd: Reg32, rs1: Reg32, rs2: Reg32)
| RV_DIV (rd: Reg32, rs1: Reg32, rs2: Reg32)
| RV_DIVU (rd: Reg32, rs1: Reg32, rs2: Reg32)
| RV_REM (rd: Reg32, rs1: Reg32, rs2: Reg32)
| RV_REMU (rd: Reg32, rs1: Reg32, rs2: Reg32)

// control and status register extension
datatype ins32CSR =
| RISC_ECALL
| RISC_EBREAK
| RISC_URET
| RISC_SRET
| RISC_MRET
| RISC_WFI
| RISC_SFENCE_VMA (rs1: Reg32, rs2: Reg32)
| RISC_CSRRW (rd: Reg32, rs1: Reg32, csr12: uint32)
| RISC_CSRRS (rd: Reg32, rs1: Reg32, csr12: uint32)
| RISC_CSRRC (rd: Reg32, rs1: Reg32, csr12: uint32)
| RISC_CSRRWI (rd: Reg32, zimm: uint32, csr12: uint32)
| RISC_CSRRSI (rd: Reg32, zimm: uint32, csr12: uint32)
| RISC_CSRRCI (rd: Reg32, zimm: uint32, csr12: uint32)

datatype rv_ins32 = ins32I(ins: ins32I)| ins32M(ins: ins32M) | ins32CSR(ins: ins32CSR)

datatype code =
| Ins32(ins: rv_ins32)
| Block(block: codes)
// | IfElse(ifCond: ifCond, ifTrue:code, ifFalse:code)
| While(whileCond: whileCond, whileBody: code)

datatype codes = CNil | va_CCons(hd: code, tl: codes)

// todo
datatype whileCond =
    | RegCond(r: Reg32)
    | ImmCond(c: uint32)

datatype state = state(
    regs: map<Reg32, uint32>, // 32-bit registers
    mem: map<int, uint32>,
    ok: bool)

predicate valid_state(s: state)
{
    (forall r :: r in s.regs)
}

predicate IsUInt32(i: int) { 0 <= i < 0x1_0000_0000 }

predicate ValidRegister32(regs: map<Reg32, uint32>, r: Reg32)
{
    r in regs
}

function eval_reg(regs: map<Reg32, uint32>, r: Reg32) : uint32
{
    if !ValidRegister32(regs, r) then 24 // TODO: better error message
    else regs[r]
}

predicate ValidSourceRegister32(s: state, r: Reg32)
{
    ValidRegister32(s.regs, r)
}

predicate ValidDestinationRegister32(s: state, r: Reg32)
{
    ValidRegister32(s.regs, r)
}

function eval_reg32(s: state, r: Reg32) : uint32
{
    if !ValidSourceRegister32(s, r) then
        42
    else
        s.regs[r]
}

predicate evalIns32(ins: rv_ins32, s: state, r: state)
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
        case RegCond(r) => eval_reg(s.regs, r)
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
        case Block(block) => evalBlock(block, s, r)
        //case IfElse(cond, ifT, ifF) => evalIfElse(cond, ifT, ifF, s, r)
        case While(cond, body) => evalWhile(body, eval_cond(s, cond), s, r)
}

}
