include "../spec/def.dfy"

module _vale {

import opened bignum_def

type opr = operand

////////////////////////////////////////////////////////////////////////
//
//  Connecting Vale types to Dafny types
//
////////////////////////////////////////////////////////////////////////

type va_code = code
type va_codes = codes
type va_state = state

////////////////////////////////////////////////////////////////////////
//
//  Connecting Vale functions to Dafny functions
//
////////////////////////////////////////////////////////////////////////

function va_get_ok(s:va_state):bool { s.ok }
function va_get_reg32(r:Reg32, s:va_state):uint32 requires r in s.regs32 { s.regs32[r] }
function va_get_reg256(r:Reg256, s:va_state):Bignum requires r in s.regs256 { s.regs256[r] }

// TODO: Distinguish between flag groups 1 and 2
function va_get_flags(f:int, s:va_state):bool requires f in s.flags { s.flags[f] }
function va_get_stack(s:va_state):Stack { s.stack }

function va_update_ok(sM:va_state, sK:va_state):va_state { sK.(ok := sM.ok) }

function va_update_reg32(r:Reg32, sM:va_state, sK:va_state):va_state
    requires r in sM.regs32
{ sK.(regs32 := sK.regs32[r := sM.regs[r]]) }

function va_update_reg256(r:Reg256, sM:va_state, sK:va_state):va_state
    requires r in sM.regs256
{ sK.(regs256 := sK.regs256[r := sM.regs[r]]) }

function va_update_flags(f:int, sM:va_state, sK:va_state):va_state
    requires f in sM.flags
{ sK.(flags := sK.flags[f := sM.flags[f]]) }

function va_update_stack(sM:va_state, sK:va_state):va_state { sK.(stack := sM.stack) }

type va_value_opr32 = uint32
type va_operand_opr32 = operand
predicate is_src_opr32(o:opr, s:va_state) { (o.OConst? && IsUInt32(o.n)) || (o.OReg? && !o.r.Reg32?) }

predicate va_is_src_opr32(o:opr, s:va_state) { (o.OConst? && IsUInt32(o.n)) || (o.OReg? && !o.r.Reg256? && o.r in s.regs32 && IsUInt32(s.regs[o.r])) }
predicate va_is_dst_opr32(o:opr, s:va_state) { o.OReg? && !o.r.Reg256? && o.r in s.regs32 && IsUInt32(s.regs[o.r]) }

type va_value_opr256 = Bignum
type va_operand_opr256 = operand
predicate va_is_src_opr256(o:opr, s:va_state) { o.OReg? && o.r.Reg256? && 0 <= o.r.reg256 <= 31 }
predicate va_is_dst_opr256(o:opr, s:va_state) { o.OReg? && o.r.Reg256? && 0 <= o.r.reg256 <= 31 }

function va_eval_opr32(s:va_state, o:opr):uint32
    requires is_src_opr32(o, s);
{
    eval_op32(s, o)
}

function va_eval_opr256(s:va_state, o:opr):Bignum
    requires va_is_src_opr256(o, s);
{
    eval_op256(s, o)
}

function va_eval_opr256(s:va_state, o:opr):Bignum
    requires va_is_src_opr256(o, s);
    requires o.r.reg256 in s.reg256;
{
    s.reg256[o.r.reg256]
}

function va_update_operand_opr32(o:opr, sM:va_state, sK:va_state):va_state
    requires o.OReg?;
    requires o.r in sM.regs;
    requires o.r.Reg256? ==> o.r.reg256 in sM.reg256;
{
    va_update_operand(o, sM, sK)
}

function va_update_operand_opr256(o:opr, sM:va_state, sK:va_state):va_state
    requires o.OReg?;
    requires o.r in sM.reg256;
    requires o.r.Reg256? ==> o.r.reg256 in sM.reg256;
{
    va_update_operand(o, sM, sK)
}
}