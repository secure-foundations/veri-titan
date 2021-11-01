include "../../lib/signed_bv_ops.dfy"

module rv_machine {
    import opened bv_ops // bit-vector operations

    const DMEM_LIMIT: int := 0x80000

    /* registers definitions */
    type reg_index = uint5 // 32 registers
      
    datatype reg32_t = | GPR(index: reg_index) // 32 32-bit registers, x0 is always zero

    type gprs_t = gprs : seq<uint32> | |gprs| == 32 witness *

    
    /* gpr_view definion */

    datatype uint64_raw = uint64_cons(
        lh: uint32, uh: uint32, full: uint64)

    type uint64_view_t = num: uint64_raw |
        && num.lh == uint64_lh(num.full)
        && num.uh == uint64_uh(num.full)
        witness *

    predicate valid_uint64_view(
        num: uint64_view_t,
        lh: uint32, uh: uint32)
    {
        && lh == num.lh
        && uh == num.uh
    }

    /* int64 views are constructed from UNSIGNED uint32 values in
    registers, so that we always keep the assumption that values in a
    register are unsigned but can be VIEWED as signed */
    datatype int64_raw = int64_cons(
        lh: uint32, uh: uint32, full: int64)

    type int64_view_t = num: int64_raw |
        && num.lh == uint64_lh(to_2s_complement_bv64(num.full))
        && num.uh == uint64_uh(to_2s_complement_bv64(num.full)) 
        witness *

    lemma lemma_int64_half_split(num: int64_view_t)
        ensures num.lh + num.uh * BASE_32 == to_2s_complement_bv64(num.full);
    {
        reveal uint64_lh();
        reveal uint64_uh();
        assert num.lh + num.uh * BASE_32 == to_2s_complement_bv64(num.full);
    }

    predicate valid_int64_view(
        num: int64_view_t,
        lh: uint32, uh: uint32)
    {
        && lh == num.lh
        && uh == num.uh
    }
    
    lemma lemma_int64_negative_one(num: int64_view_t)
        requires num.lh == BASE_32 - 1
        requires num.uh == BASE_32 - 1
        ensures num.full == -1
    {
        lemma_int64_half_split(num);
        assert num.lh + num.uh * BASE_32 == to_2s_complement_bv64(num.full);
        assert num.lh + num.uh * BASE_32 == BASE_64 - 1;
        assert num.full == -1;
    }

   /* memory definitions */ 

    type mem_t = map<int, seq<uint32>>

    predicate mem_base_addr_valid(mem: mem_t, addr: int, size: nat)
    {
        && addr in mem
        // buff is not empty
        && |mem[addr]| == size != 0
        // buff does not extend beyond mem limit
        && addr + 4 * size <= DMEM_LIMIT
    }

    /* iter_t definion */

    datatype iter_t = iter_cons(base_addr: int, index: nat, buff: seq<uint32>)

    function lw_next_iter(iter: iter_t): iter_t
    {
        iter.(index := iter.index + 1)
    }

    function lw_prev_iter(iter: iter_t): iter_t
    {
        if iter.index == 0 then
            iter
        else
            iter.(index := iter.index - 1)
    }

    function sw_iter(iter: iter_t, value: uint32): iter_t
        requires iter.index < |iter.buff|
    {
        iter.(buff := iter.buff[iter.index := value])
    }
    
    function sw_next_iter(iter: iter_t, value: uint32): iter_t
        requires iter.index < |iter.buff|
    {
        iter.(index := iter.index + 1)
            .(buff := iter.buff[iter.index := value])
    }

    predicate iter_inv(iter: iter_t, mem: mem_t, address: int)
    {
        var base_addr := iter.base_addr;
        // address is correct
        && address == base_addr + 4 * iter.index
        // base_addr points to a valid buffer
        && mem_base_addr_valid(mem, base_addr, |iter.buff|)
        // the view is consistent with mem
        && mem[base_addr] == iter.buff
        // the index is within bound (or at end)
        && iter.index <= |iter.buff|
    }

    predicate iter_safe(iter: iter_t, mem: mem_t, address: int)
    {
        && iter_inv(iter, mem, address)
        // tighter constraint so we can dereference
        && iter.index < |iter.buff|
    }


    /* state definition */

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

    | RV_ADDI (rd: reg32_t, rs1: reg32_t, simm12: int32) // sign extends, ignore overflow
    | RV_SLLI (rd: reg32_t, rs1: reg32_t, shamt6: uint32) // logical left shift
    | RV_SLTI (rd: reg32_t, rs1: reg32_t, simm12: int32) // sign extend, 1 if rs1 (signed) < imm, else 0
    | RV_SLTIU (rd: reg32_t, rs1: reg32_t, imm12: uint32) // compare both vals as unsigned.
    | RV_XORI (rd: reg32_t, rs1: reg32_t, imm12: uint32)
    | RV_ORI (rd: reg32_t, rs1: reg32_t, imm12: uint32)
    | RV_ANDI (rd: reg32_t, rs1: reg32_t, imm12: uint32)
    | RV_SRLI (rd: reg32_t, rs1: reg32_t, shamt6: uint32) // logical right shift
    | RV_SRAI (rd: reg32_t, rs1: reg32_t, shamt6: uint32) // arithmetic right shift

    | RV_AUIPC (rd: reg32_t, oimm20: uint32)

    | RV_SB (rs1: reg32_t, rs2: reg32_t, imm12: uint32)
    | RV_SH (rs1: reg32_t, rs2: reg32_t, imm12: uint32)
    | RV_SW (rs1: reg32_t, rs2: reg32_t, imm12: uint32)

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
    | RV_LI (rd: reg32_t, imm20: uint32)

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

    datatype cmp = Eq | Ne | Le | Ge | Lt | Gt
    
    datatype cond = Cmp(op:cmp, r1:reg32_t, r2:reg32_t)

    datatype code =
    | Ins32(ins: ins32)
    | Block(block: codes)
    | While(whileCond: cond, whileBody: code)
    | IfElse(ifCond: cond, ifTrue:code, ifFalse:code)
    // | Procedure(proc: codes, name: string) // TODO: direct call semantics
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
          case Ne => s.eval_reg32(r1) != s.eval_reg32(r2)
          case Le  => s.eval_reg32(r1) <= s.eval_reg32(r2)
          case Ge  => s.eval_reg32(r1) >= s.eval_reg32(r2)
          case Lt  => s.eval_reg32(r1) < s.eval_reg32(r2)
          case Gt  => s.eval_reg32(r1) > s.eval_reg32(r2)
    }

    function eval_cond(s:state, c:cond):bool
    {
        eval_cmp(s, c.op, c.r1, c.r2)
    }

    predicate eval_if_else(cond:cond, ifT:code, ifF:code, s:state, r:state)
        decreases if eval_cond(s, cond) then ifT else ifF
    {
        if s.ok then
            (if eval_cond(s, cond) then eval_code(ifT, s, r) else eval_code(ifF, s, r))
        else
            !r.ok
    }

    predicate eval_while(condition:cond, body:code, n: nat, s: state, r: state)
        decreases body, n
    {
        if s.ok then
            if n == 0 then
                !eval_cond(s, condition) && (s == r)
            else
              exists s': state :: eval_cond(s, condition)
                      && eval_code(body, s, s')
                      && eval_while(condition, body, n - 1, s', r)
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
            case IfElse(cond, ifT, ifF) => eval_if_else(cond, ifT, ifF, s, r)
            case Comment(com) => s == r
    }
}
