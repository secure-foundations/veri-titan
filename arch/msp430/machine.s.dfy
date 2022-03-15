include "../../lib/bv16_ops.dfy"
include "flat.s.dfy"
// include "../../lib/bv20_ops.dfy"

module msp_machine {
    import opened integers
    import opened bv16_ops
    import opened flat

    /* registers definitions */

    // R0 R1, R2 are special 
    type int16 = sint

    type reg_idx = i: nat | 4 <= i <= 15 witness 4

    datatype reg_t =  
        // | PC
        | SP
        | R(i: reg_idx)

    /* state definition */

    type regs_t = regs : seq<uint16> | |regs| == 16 witness *

    datatype operand_t = 
        | Reg(r: reg_t)
        | Idx(r: reg_t, index: uint16)
        | Abs(s: string)
        | RegIndir(r: reg_t, inc: bool)
        | Imm(i: int16)
    
    datatype flags_t = flags_cons(msb: uint1, zero: uint1, cf: uint1 /*, over: uint1 */)

    function method update_flags(value: uint16, carry: uint1): flags_t
    {
        flags_cons(msb(value), if value == 0 then 1 else 0, carry)
    }

    function method msp_add(x: uint16, y: uint16): (uint16, flags_t)
    {
        var (z, c) := addc(x, y, 0);
        (z, update_flags(z, c))
    }

    function method msp_addc(x: uint16, y: uint16, flags: flags_t): (uint16, flags_t)
    {
        var (z, c) := addc(x, y, flags.cf);
        (z, update_flags(z, c))
    }

    function method msp_sub(x: uint16, y: uint16): (uint16, flags_t)
    {
        var (z, c) := subb(x, y, 0);
        (z, update_flags(z, c))
    }

    function method msp_subc(x: uint16, y: uint16, flags: flags_t): (uint16, flags_t)
    {
        var (z, c) := subb(x, y, flags.cf);
        (z, update_flags(z, c))
    }

    datatype state = state(
        regs: regs_t,
        sp: uint16,
        flat: flat_t,
        flags: flags_t,
        ok: bool)
    {
        function read_reg(r: reg_t): uint16
        {
            if r.SP? then sp else regs[r.i]
        }

        // will overrite higher bits
        function write_reg(r: reg_t, value: uint16): state
        {
            if r.SP? then
                this.(sp := value)
            else 
                this.(regs := regs[r.i := value])
        }
    }

    predicate valid_push_pop_m(r: reg_t, n: nat)
    {
        && n != 0
        && r.R?
        && 4 <= r.i - n + 1 <= r.i
    }

    function pushm_w_seq(state: state, r: reg_t, n: uint16): seq<uint16>
        requires valid_push_pop_m(r, n)
    {
        state.regs[r.i-n+1..r.i+1]
    }

    function {:opaque} popm_w_seq(old_regs: regs_t, r: reg_t, n: nat, s: seq<uint16>): (new_regs: regs_t)
        requires valid_push_pop_m(r, n)
        requires |s| == n
        ensures new_regs[..r.i-n+1] == old_regs[..r.i-n+1]
        ensures new_regs[r.i-n+1..r.i+1] == s
        ensures new_regs[r.i+1..] == old_regs[r.i+1..]
    {
        var start := r.i - n + 1;
        var end := r.i + 1;
        var new_regs := seq(16, i requires 0 <= i < 16 => 
            if start <= i < end then s[i - r.i + n - 1] else old_regs[i]);
        assert new_regs[start..end] == s;
        new_regs
    }

    function eval_operand(s: state, op: operand_t): uint16
        // requires op.Reg? || op.Imm?
    {
        match op
            case Reg(r) => s.read_reg(r)
            case Imm(i) => to_uint16(i)
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
        | MSP_SUBC_W(src: operand_t, dst: operand_t)
        | MSP_MOV_W(src: operand_t, dst: operand_t)
        | MSP_MOV_B(src: operand_t, dst: operand_t)
        // | MSP_CMP_W(src: operand_t, dst: operand_t)
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
