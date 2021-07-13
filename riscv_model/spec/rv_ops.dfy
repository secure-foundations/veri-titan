include "rv_consts.dfy"
include "bv_ops.dfy"

include "../lib/powers.dfy"
include "../lib/congruences.dfy"

module rv_ops {

    import opened bv_ops // bit-vector operations
    import opened rv_consts // RISC-V constants

    import opened powers
    import opened congruences

    /* registers definitions */
    type reg_index = uint5 // 32 registers
      
    datatype reg32_t = | GPR(index: reg_index) // 32 32-bit registers, x0 is always zero

    type gprs_t = gprs : seq<uint32> | |gprs| == 32 witness *

    type mem_t = map<int, uint32>

    predicate mem_addr_valid(mem: mem_t, addr: int)
    {
        && addr in mem
    }

    predicate mem_addr_mapped(mem: mem_t, addr: int, value: uint32)
    {
        && mem_addr_valid(mem, addr)
        && mem[addr] == value
    }

    datatype state = state(
        gprs: gprs_t, // 32-bit registers
        mem: mem_t,
        ok: bool)
    {
        function eval_reg32(r: reg32_t) : uint32
        {
            if r.index == 0 then 0
            else gprs[r.index]
        }
    }

    predicate valid_state(s: state)
    {
        s.ok
    }
    
    // base integer instruction set, 32-bit
    datatype ins32 =
    | RV_LB(rd: reg32_t, rs1: reg32_t, oimm12: uint32)
    | RV_LH (rd: reg32_t, rs1: reg32_t, oimm12: uint32)
    | RV_LW (rd: reg32_t, rs1: reg32_t, oimm12: uint32)
    | RV_LBU (rd: reg32_t, rs1: reg32_t, oimm12: uint32)
    | RV_LHU (rd: reg32_t, rs1: reg32_t, oimm12: uint32)

    | RV_FENCE (pred: uint32, succ: uint32)
    | RV_FENCE_I

    | RV_ADDI (rd: reg32_t, rs1: reg32_t, imm12: uint32) // sign extends, ignore overflow
    | RV_SLLI (rd: reg32_t, rs1: reg32_t, shamt6: uint32) // logical left shift
    | RV_SLTI (rd: reg32_t, rs1: reg32_t, imm12: uint32) // sign extend, 1 if rs1 (signed) < imm, else 0
    | RV_SLTIU (rd: reg32_t, rs1: reg32_t, imm12: uint32) // compare both vals as unsigned.
    | RV_XORI (rd: reg32_t, rs1: reg32_t, imm12: uint32)
    | RV_ORI (rd: reg32_t, rs1: reg32_t, imm12: uint32)
    | RV_ANDI (rd: reg32_t, rs1: reg32_t, imm12: uint32)
    | RV_SRLI (rd: reg32_t, rs1: reg32_t, shamt6: uint32) // logical right shift
    | RV_SRAI (rd: reg32_t, rs1: reg32_t, shamt6: uint32) // arithmetic right shift

    | RV_AUIPC (rd: reg32_t, oimm20: uint32)

    | RV_SB (rs1: reg32_t, rs2: reg32_t, simm12: uint32)
    | RV_SH (rs1: reg32_t, rs2: reg32_t, simm12: uint32)
    | RV_SW (rs1: reg32_t, rs2: reg32_t, simm12: uint32)

    | RV_ADD (rd: reg32_t, rs1: reg32_t, rs2: reg32_t) // ignore overflow
    | RV_SUB (rd: reg32_t, rs1: reg32_t, rs2: reg32_t) // ignore overflow
    | RV_SLL (rd: reg32_t, rs1: reg32_t, rs2: reg32_t) // shift logical left by "lower 5 bits of rs2"
    | RV_SLT (rd: reg32_t, rs1: reg32_t, rs2: reg32_t) // signed less than
    | RV_SLTU (rd: reg32_t, rs1: reg32_t, rs2: reg32_t) // unsigned less than
    | RV_XOR (rd: reg32_t, rs1: reg32_t, rs2: reg32_t) // bitwise
    | RV_SRL (rd: reg32_t, rs1: reg32_t, rs2: reg32_t) // shift logical right by "lower 5 bits of rs2"
    | RV_SRA (rd: reg32_t, rs1: reg32_t, rs2: reg32_t) // shift arithmetic right by "lower 5 bits of rs2"
    | RV_OR (rd: reg32_t, rs1: reg32_t, rs2: reg32_t) // bitwise
    | RV_AND (rd: reg32_t, rs1: reg32_t, rs2: reg32_t) // bitwise

    | RV_LUI (rd: reg32_t, imm20: uint32)

    // | RV_BEQ (rs1: reg32_t, rs2: reg32_t, sbimm12: uint32)
    // | RV_BNE (rs1: reg32_t, rs2: reg32_t, sbimm12: uint32)
    // | RV_BLT (rs1: reg32_t, rs2: reg32_t, sbimm12: uint32)
    // | RV_BGE (rs1: reg32_t, rs2: reg32_t, sbimm12: uint32)
    // | RV_BLTU (rs1: reg32_t, rs2: reg32_t, sbimm12: uint32)
    // | RV_BGEU (rs1: reg32_t, rs2: reg32_t, sbimm12: uint32)
    // 
    // | RV_JALR (rd: reg32_t, rs1: reg32_t, oimm12: uint32)
    // | RV_JAL (rd: reg32_t, jimm20: uint32)

    // standard extension for integer mult and div, 32-bit
    | RV_MUL (rd: reg32_t, rs1: reg32_t, rs2: reg32_t)
    | RV_MULH (rd: reg32_t, rs1: reg32_t, rs2: reg32_t)
    | RV_MULHSU (rd: reg32_t, rs1: reg32_t, rs2: reg32_t)
    | RV_MULHU (rd: reg32_t, rs1: reg32_t, rs2: reg32_t)
    | RV_DIV (rd: reg32_t, rs1: reg32_t, rs2: reg32_t)
    | RV_DIVU (rd: reg32_t, rs1: reg32_t, rs2: reg32_t)
    | RV_REM (rd: reg32_t, rs1: reg32_t, rs2: reg32_t)
    | RV_REMU (rd: reg32_t, rs1: reg32_t, rs2: reg32_t)

    // control and status register extension
    | RISC_ECALL
    | RISC_EBREAK
    | RISC_URET
    | RISC_SRET
    | RISC_MRET
    | RISC_WFI
    | RISC_SFENCE_VMA (rs1: reg32_t, rs2: reg32_t)
    | RISC_CSRRW (rd: reg32_t, rs1: reg32_t, csr12: uint32)
    | RISC_CSRRS (rd: reg32_t, rs1: reg32_t, csr12: uint32)
    | RISC_CSRRC (rd: reg32_t, rs1: reg32_t, csr12: uint32)
    | RISC_CSRRWI (rd: reg32_t, zimm: uint32, csr12: uint32)
    | RISC_CSRRSI (rd: reg32_t, zimm: uint32, csr12: uint32)
    | RISC_CSRRCI (rd: reg32_t, zimm: uint32, csr12: uint32)

    predicate eval_ins32(ins: ins32, s: state, r: state)
        {
            if !s.ok then
                !r.ok
            else
                r.ok && (valid_state(s) ==> valid_state(r))
        }

    /* control flow definitions */

    datatype cmp = Eq | Neq | Le | Ge | Lt | Gt
    
    datatype cond = Cmp(op:cmp, r1:reg32_t, r2:reg32_t)

    datatype code =
    | Ins32(ins: ins32)
    | Block(block: codes)
    | While(whileCond: cond, whileBody: code)
    | Comment(com: string)

    datatype codes =
      | CNil
      | va_CCons(hd: code, tl: codes)

predicate eval_block(block: codes, s: state, r: state)
    {
        if block.CNil? then
            r == s
        else
            exists r': state :: eval_code(block.hd, s, r') && eval_block(block.tl, r', r)
    }

    function eval_cmp(s:state, c:cmp, r1:reg32_t, r2:reg32_t):bool
    {
        match c
          case Eq  => s.eval_reg32(r1) == s.eval_reg32(r2)
          case Neq => s.eval_reg32(r1) != s.eval_reg32(r2)
          case Le  => s.eval_reg32(r1) <= s.eval_reg32(r2)
          case Ge  => s.eval_reg32(r1) >= s.eval_reg32(r2)
          case Lt  => s.eval_reg32(r1) < s.eval_reg32(r2)
          case Gt  => s.eval_reg32(r1) > s.eval_reg32(r2)
    }

    function eval_cond(s:state, c:cond):bool
    {
        eval_cmp(s, c.op, c.r1, c.r2)
    }

    predicate eval_while(condition:cond, body:code, n: nat, s: state, r: state)
        decreases body, n
    {
        if s.ok then
            if n == 0 then
                !eval_cond(s, condition) && (s == r)
            else
              exists loop_start: state, loop_end: state :: eval_cond(s, condition)
                      && eval_code(body, loop_start, loop_end)
                      && eval_while(condition, body, n - 1, loop_end, r)
        else
            !r.ok
    }

    predicate eval_code(c: code, s: state, r: state)
        decreases c, 0
    {
        match c
            case Ins32(ins) => eval_ins32(ins, s, r)
            case Block(block) => eval_block(block, s, r)
            case While(condition, body) => exists n:nat :: eval_while(condition, body, n, s, r)
            case Comment(com) => s == r
    }
}
