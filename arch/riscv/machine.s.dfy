include "../../lib/bv32_ops.dfy"

module rv_machine {
    import opened integers
    import opened bv32_ops

    const DMEM_LIMIT: int := 0x80000

    /* registers definitions */

    datatype reg32_t =  
        | X0 // hardwired to 0, ignores writes	n/a
        | RA // x1		return address for jumps	no
        | SP // x2		stack pointer	yes
        | GP // x3		global pointer	n/a
        | TP // x4		thread pointer	n/a
        | T0 // x5		temporary register 0	no
        | T1 // x6		temporary register 1	no
        | T2 // x7		temporary register 2	no
        | S0 // x8	 	saved register 0 or frame pointer	yes
        | S1 // x9		saved register 1	yes
        | A0 // x10		return value or function argument 0	no
        | A1 // x11		return value or function argument 1	no
        | A2 // x12		function argument 2	no
        | A3 // x13		function argument 3	no
        | A4 // x14		function argument 4	no
        | A5 // x15		function argument 5	no
        | A6 // x16		function argument 6	no
        | A7 // x17		function argument 7	no
        | S2 // x18		saved register 2	yes
        | S3 // x19		saved register 3	yes
        | S4 // x20		saved register 4	yes
        | S5 // x21		saved register 5	yes
        | S6 // x22		saved register 6	yes
        | S7 // x23		saved register 7	yes
        | S8 // x24		saved register 8	yes
        | S9 // x25		saved register 9	yes
        | S10// x26		saved register 10	yes
        | S11// x27		saved register 11	yes
        | T3 // x28		temporary register 3	no
        | T4 // x29		temporary register 4	no
        | T5 // x30		temporary register 5	no
        | T6 // x31		temporary register 6	no
        // pc	(none)	program counter	n/a

    function method reg32_to_index(r: reg32_t): nat
    {
        match r {
            case X0 => 0
            case RA => 1
            case SP => 2
            case GP => 3
            case TP => 4
            case T0 => 5
            case T1 => 6
            case T2 => 7
            case S0 => 8
            case S1 => 9
            case A0 => 10
            case A1 => 11
            case A2 => 12
            case A3 => 13
            case A4 => 14
            case A5 => 15
            case A6 => 16
            case A7 => 17
            case S2 => 18
            case S3 => 19
            case S4 => 20
            case S5 => 21
            case S6 => 22
            case S7 => 23
            case S8 => 24
            case S9 => 25
            case S10 => 26
            case S11 => 27
            case T3 => 28
            case T4 => 29
            case T5 => 30
            case T6 => 31
        }
    }

    // datatype uint64_raw = uint64_cons(
    //     lh: uint32, uh: uint32, full: uint64)

    // type uint64_view_t = num: uint64_raw |
    //     && num.lh == dw_lh(num.full)
    //     && num.uh == dw_uh(num.full)
    //     witness *

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

    predicate valid_frame_ptr(mem: mem_t, address: int, words: nat)
    {
        && address in mem
        && address >= 0
        && |mem[address]| == words
    }

    /* state definition */

    type regs_t = regs : seq<uint32> | |regs| == 32 witness *

    datatype state = state(
        regs: regs_t, // 32-bit registers
        mem: mem_t,
        ok: bool)
    {
        function read_reg32(r: reg32_t) : uint32
        {
            if r.X0? then 0 
            else regs[reg32_to_index(r)]
        }

        function write_reg32(r: reg32_t, value: uint32): state
        {
            this.(regs := this.regs[reg32_to_index(r) := value])
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
    | IfElse(ifCond: cond, ifTrue: code, ifFalse: code)
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
          case Eq  => s.read_reg32(r1) == s.read_reg32(r2)
          case Ne => s.read_reg32(r1) != s.read_reg32(r2)
          case Le  => s.read_reg32(r1) <= s.read_reg32(r2)
          case Ge  => s.read_reg32(r1) >= s.read_reg32(r2)
          case Lt  => s.read_reg32(r1) < s.read_reg32(r2)
          case Gt  => s.read_reg32(r1) > s.read_reg32(r2)
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
