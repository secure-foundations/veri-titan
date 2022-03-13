include "../../lib/bv16_ops.dfy"
include "flat.s.dfy"
// include "../../lib/bv20_ops.dfy"

module msp_machine {
    import opened integers
    import opened bv16_ops
    import opened flat

    /* registers definitions */

    datatype reg_t =  
        // | PC
        | SP
        // | R2
        | R3
        | R4
        | R5
        | R6
        | R7
        | R8
        | R9
        | R10
        | R11
        | R12
        | R13
        | R14
        | R15

    /* state definition */

    type regs_t = map<reg_t, uint16>

    // function method truncate_20_to_16(v: uint20): uint16
    // {
    //     v % BASE_16
    // }

    datatype operand_t = 
        | Reg(r: reg_t)
        | Idx(r: reg_t, index: uint16)
        | RegIndir(r: reg_t, inc: bool)
        | Imm(i: uint16)
    
    datatype state = state(
        regs: regs_t,
        flat: flat_t,
        ok: bool)
    {
        function read_reg(r: reg_t): uint16
        {
            if r in regs then regs[r] else 0
        }

        // will overrite higher bits
        function write_reg(r: reg_t, value: uint16): state
        {
            this.(regs := this.regs[r := value])
        }
    }

    function eval_operand(s: state, op: operand_t): uint16
        // requires op.Reg? || op.Imm?
    {
        match op
            case Reg(r) => s.read_reg(r)
            case Imm(i) => i
            case _ => 0
    }

    predicate valid_state(s: state)
    {
        s.ok
    }

    datatype ins_t = 
        | MSP_ADD_W(src: operand_t, dst: operand_t)
        | MSP_ADDC_W(src: operand_t, dst: operand_t)
        | MSP_SUB_W(src: operand_t, dst: operand_t)
        | MSP_MOV_W(src: operand_t, dst: operand_t)
        | MSP_MOV_B(src: operand_t, dst: operand_t)
        | MSP_CMP_W(src: operand_t, dst: operand_t)
        | MSP_RRAX_W(dst: operand_t)
        | MSP_PUSHM_W(dst: operand_t, n: operand_t)
        | MSP_POPM_W(dst: operand_t, n: operand_t)
        // BR
        // RET
        // CALL

    predicate eval_ins(ins: ins_t, s: state, r: state)
    {
        if !s.ok then
            !r.ok
        else
            r.ok && (valid_state(s) ==> valid_state(r))
    }

    /* control flow definitions */

    datatype cond =
        | Eq(o1: operand_t, o2: operand_t)
        | Ne(o1: operand_t, o2: operand_t)
        | LO(o1: operand_t, o2: operand_t) // Jump if lower (unsigned)
        | HS(o1: operand_t, o2: operand_t) // Jump if higher or same (unsigned)
    
    datatype code =
        | Ins(ins: ins_t)
        | Block(block: codes)
        | While(whileCond: cond, whileBody: code)
        | IfElse(ifCond: cond, ifTrue: code, ifFalse: code)
        | Function(name: string, functionBody: codes)
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

    function eval_cond(s: state, c: cond):bool
    {
        match c
          case Eq(o1, o2)  => (eval_operand(s, o1) == eval_operand(s, o2))
          case Ne(o1, o2)  => (eval_operand(s, o1) != eval_operand(s, o2))
          case LO(o1, o2)  => (eval_operand(s, o1) < eval_operand(s, o2))
          case HS(o1, o2)  => (eval_operand(s, o1) >= eval_operand(s, o2))
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
            case Ins(ins) => eval_ins(ins, s, r)
            case Block(block) => eval_block(block, s, r)
            case While(condition, body) => exists n:nat :: eval_while(condition, body, n, s, r)
            case Function(name, body) => eval_block(body, s, r)
            case IfElse(cond, ifT, ifF) => eval_if_else(cond, ifT, ifF, s, r)
            case Comment(com) => s == r
    }
}
