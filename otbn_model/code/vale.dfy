include "../spec/def.dfy"

module bignum_vale {

import opened types	
import opened bignum_def

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
function va_get_reg32(r:Reg32, s:va_state):uint32 requires r in s.xregs { s.xregs[r] }
function va_get_reg256(r:Reg256, s:va_state):Bignum requires r in s.wregs { s.wregs[r] }

// TODO: Distinguish between flag groups 1 and 2
//function va_get_flags(f:int, s:va_state):bool requires f in s.flags { s.flags[f] }
function va_get_stack(s:va_state):Stack { s.stack }

function va_update_ok(sM:va_state, sK:va_state):va_state { sK.(ok := sM.ok) }

function va_update_reg32(r:Reg32, sM:va_state, sK:va_state):va_state
    requires r in sM.xregs
{ sK.(xregs := sK.xregs[r := sM.xregs[r]]) }

function va_update_reg256(r:Reg256, sM:va_state, sK:va_state):va_state
    requires r in sM.wregs
{ sK.(wregs := sK.wregs[r := sM.wregs[r]]) }

//function va_update_flags(f:int, sM:va_state, sK:va_state):va_state
//    requires f in sM.flags
//{ sK.(flags := sK.flags[f := sM.flags[f]]) }

function va_update_stack(sM:va_state, sK:va_state):va_state { sK.(stack := sM.stack) }

type va_value_reg32 = uint32
type va_operand_reg32 = Reg32
//predicate is_src_reg32(r:Reg32, s:va_state) { r.Rnd? || (r.Gpr? && 0 <= r.x <= 31)}

predicate va_is_src_reg32(r:Reg32, s:va_state) { (r.Gpr? ==> 0 <= r.x <= 31) && r in s.xregs && IsUInt32(s.xregs[r]) }
predicate va_is_dst_reg32(r:Reg32, s:va_state) { (r in s.xregs && IsUInt32(s.xregs[r]) && r.Gpr? && 0 <= r.x <= 31) }

function va_eval_reg32(s:va_state, r:Reg32):uint32
  requires va_is_src_reg32(r, s);
{
    s.xregs[r]
}

function va_update_operand_reg32(r:Reg32, sM:va_state, sK:va_state):va_state
    requires r in sM.xregs;
    requires r.Gpr? ==> ValidRegisterIndex(r.x);
{
    va_update_reg32(r, sM, sK)
}

predicate va_state_eq(s0:va_state, s1:va_state)
{
    s0.xregs == s1.xregs
 && s0.wregs == s1.wregs
// && s0.flags == s1.flags
 && s0.stack == s1.stack
 && s0.ok == s1.ok
}

predicate{:opaque} evalCodeOpaque(c:code, s0:state, sN:state)
{
    evalCode(c, s0, sN)
}

predicate eval_code(c:code, s:state, r:state)
{
    s.ok ==> evalCodeOpaque(c, s, r)
}

function method va_CNil():codes { CNil }
predicate cHeadIs(b:codes, c:code) { b.va_CCons? && b.hd == c }
predicate cTailIs(b:codes, t:codes) { b.va_CCons? && b.tl == t }

predicate va_require(b0:codes, c1:code, s0:va_state, sN:va_state)
{
    cHeadIs(b0, c1)
 && eval_code(Block(b0), s0, sN)
 && BN_ValidState(s0)
}

// Weaker form of eval_code that we can actually ensure generically in instructions
predicate eval_weak(c:code, s:state, r:state)
{
    s.ok && r.ok ==> evalCodeOpaque(c, s, r)
}

predicate va_ensure(b0:codes, b1:codes, s0:va_state, s1:va_state, sN:va_state)
{
    cTailIs(b0, b1)
 && eval_weak(b0.hd, s0, s1)
 && eval_code(Block(b1), s1, sN)
 && BN_ValidState(s1)
}

lemma va_ins_lemma(b0:code, s0:va_state)
{
}

function method va_op_reg32_reg32(r:Reg32):Reg32 { r }
function method va_Block(block:codes):code { Block(block) }

function method va_get_block(c:code):codes requires c.Block? { c.block }

lemma lemma_FailurePreservedByBlock(block:codes, s:state, r:state)
    requires evalBlock(block, s, r);
    ensures  !s.ok ==> !r.ok;
    decreases block;
{
    if !block.CNil? {
        var r' :| evalCode(block.hd, s, r') && evalBlock(block.tl, r', r);
        lemma_FailurePreservedByCode(block.hd, s, r');
        lemma_FailurePreservedByBlock(block.tl, r', r);
    }
}

lemma lemma_FailurePreservedByCode(c:code, s:state, r:state)
    requires evalCode(c, s, r);
    ensures  !s.ok ==> !r.ok;
{
    if c.Block? {
        lemma_FailurePreservedByBlock(c.block, s, r);
    }
}

lemma block_state_validity(block:codes, s:state, r:state)
	requires evalBlock(block, s, r);
	requires valid_state(s);
	decreases block, 0;
	ensures r.ok ==> valid_state(r);
{
	if block.va_CCons? {
		var r':state :| evalCode(block.hd, s, r') && evalBlock(block.tl, r', r);
		code_state_validity(block.hd, s, r');
		if r'.ok {
			block_state_validity(block.tl, r', s);
		}
		else {
			lemma_FailurePreservedByBlock(block.tl, r', r);
		}
	}
}

lemma code_state_validity(c:code, s:state, r:state)
    requires evalCode(c, s, r);
    requires valid_state(s);
    decreases c, 0;
    ensures  r.ok ==> valid_state(r);
{
    if r.ok {
        if c.Ins32? {
            assert valid_state(r);
        } else if c.Block? {
            block_state_validity(c.block, s, r);
				} else {
					assume false;
				}
		}
}

lemma va_lemma_empty(s:va_state, r:va_state) returns(r':va_state)
    requires eval_code(Block(va_CNil()), s, r)
    ensures  s.ok ==> r.ok
    ensures  r' == s
    ensures  s.ok ==> r == s
{
    reveal_evalCodeOpaque();
    r' := s;
}

lemma va_lemma_block(b:codes, s0:va_state, r:va_state) returns(r1:va_state, c0:code, b1:codes)
    requires b.va_CCons?
    requires eval_code(Block(b), s0, r)
    ensures  b == va_CCons(c0, b1)
    ensures  eval_code(c0, s0, r1)
		ensures BN_ValidState(s0) && r1.ok ==> BN_ValidState(r1);
    ensures  eval_code(Block(b1), r1, r)
{
    reveal_evalCodeOpaque();
    c0 := b.hd;
    b1 := b.tl;
    if s0.ok {
        assert evalBlock(b, s0, r);
        var r':state :| evalCode(b.hd, s0, r') && evalBlock(b.tl, r', r);
        c0 := b.hd;
        b1 := b.tl;
				// TODO: add in flags
        r1 := state(r'.xregs, r'.wregs, r'.stack, r'.ok);
        if BN_ValidState(s0) {
            reveal_BN_ValidState();
            code_state_validity(c0, s0, r1);
        }
        assert eval_code(c0, s0, r1);
    } else {
        // If s0 isn't okay, we can do whatever we want,
        // so we ensure r1.ok is false, and hence eval_code(*, r1, *) is trivially true
        r1 := s0;
    }
}

////////////////////////////////////////////////////////////////////////
//
//  Invariants over the state
//
////////////////////////////////////////////////////////////////////////

predicate valid_state(s:state)
{
    |s.stack| >= 0
 && (forall r :: r in s.xregs)
 && (forall t :: t in s.wregs)
}

predicate {:opaque} BN_ValidState(s:state)
    ensures BN_ValidState(s) ==> valid_state(s);
{
    valid_state(s)
}

}
