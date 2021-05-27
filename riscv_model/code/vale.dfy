include "../spec/def.dfy"

module riscv_vale {

import opened types
import opened riscv_def

////////////////////////////////////////////////////////////////////////
//
//  Connecting Vale types to Dafny types
//
////////////////////////////////////////////////////////////////////////

type va_code = code
type va_codes = codes
type va_state = state

function va_get_ok(s: va_state): bool
{
    s.ok
}

function va_get_reg32(r:Reg32, s: va_state): uint32
    requires r in s.regs
{
    s.regs[r]
}

function va_get_mem(s: va_state): map<int, uint32>
{
    s.mem
}

function va_update_mem(sM: va_state, sK: va_state): va_state
{
    sK.(mem := sM.mem)
}

function va_get_pc(s: va_state): map<int, uint32>
{
    s.pc
}

function va_update_pc(sM: va_state, sK: va_state): va_state
{
    sK.(pc := sM.pc)
}

function va_update_ok(sM: va_state, sK: va_state): va_state
{
    sK.(ok := sM.ok)
}

function va_update_reg32(r:Reg32, sM: va_state, sK: va_state): va_state
    requires r in sM.regs
{
    sK.(regs := sK.regs[r := sM.regs[r]])
}

function fst<T,Q>(t:(T, Q)) : T { t.0 }
function snd<T,Q>(t:(T, Q)) : Q { t.1 }

type va_operand_imm32 = uint32
predicate va_is_src_imm32(v:uint32, s: va_state) { true }
function va_eval_imm32(s: va_state, v:uint32):uint32 { v }
function method va_const_imm32(n:uint32):uint32 { n }

type va_operand_imm2 = uint2
predicate va_is_src_imm2(v:uint2, s: va_state) {true}
function va_eval_imm2(s: va_state, v:uint2):uint2 {v}
function method va_const_imm2(v:uint32):uint32 {v}

type va_value_reg32 = uint32
type va_operand_reg32 = Reg32

predicate va_is_src_reg32(r:Reg32, s: va_state) { r in s.regs }
predicate va_is_dst_reg32(r:Reg32, s: va_state) { r in s.regs }

predicate Valid32Addr(h: map<int, uint32>, addr:int)
{
    addr in h
}

function va_eval_reg32(s: va_state, r:Reg32):uint32
  requires va_is_src_reg32(r, s);
{
    s.regs[r]
}

function va_update_operand_reg32(r:Reg32, sM: va_state, sK: va_state): va_state
    requires r in sM.regs;
{
    va_update_reg32(r, sM, sK)
}

function mod_add(a: nat, b: nat, m: nat): nat
    requires a < m && b < m;
{
    if a + b > m then a + b - m else a + b
}

predicate va_state_eq(s0: va_state, s1: va_state)
{
    && s0.regs == s1.regs
    && s0.mem == s1.mem
    && s0.pc == s1.pc
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

predicate va_require(b0:codes, c1:code, s0: va_state, sN: va_state)
{
    && cHeadIs(b0, c1)
    && eval_code(Block(b0), s0, sN)
    && RV_ValidState(s0)
}

// Weaker form of eval_code that we can actually ensure generically in instructions
predicate eval_weak(c:code, s:state, r:state)
{
    s.ok && r.ok ==> evalCodeOpaque(c, s, r)
}

predicate va_ensure(b0:codes, b1:codes, s0: va_state, s1: va_state, sN: va_state)
{
    && cTailIs(b0, b1)
    && eval_weak(b0.hd, s0, s1)
    && eval_code(Block(b1), s1, sN)
    && RV_ValidState(s1)
}

lemma va_ins_lemma(b0:code, s0: va_state)
{
}

function method va_const_cmp(n:uint32):uint32 { n }
function method va_coerce_reg32_to_cmp(r:Reg32):Reg32 { r }

function method va_cmp_LoopImm(u:uint32):whileCond { ImmCond(u) }
function method va_cmp_Loop(r:Reg32):whileCond { RegCond(r) }

function method va_op_reg32_reg32(r:Reg32):Reg32 { r }
function method va_Block(block:codes):code { Block(block) }
function method va_While(wcond:whileCond, wcode:code):code { While(wcond, wcode) }

function method va_get_block(c:code):codes requires c.Block? { c.block }
function method va_get_whileCond(c:code):whileCond requires c.While? {c.whileCond }
function method va_get_whileBody(c:code):code requires c.While? { c.whileBody }

lemma lemma_FailurePreservedByBlock(block:codes, s:state, r:state)
    requires evalBlock(block, s, r);
    ensures !s.ok ==> !r.ok;
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
    ensures !s.ok ==> !r.ok;
{
    match c {
        case Block(b) => {
            lemma_FailurePreservedByBlock(b, s, r);
        }
        case While(c, b) => {
            var n :| evalWhile(b, n, s, r);
        }
        case Ins32(i) => {
            var r' :| evalCode(c, s, r');
        }
    }
}

// predicate BN_branchRelation(s:state, r:state, cond:bool)
// {
// 	branchRelation(s, r, cond)
// }

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
			block_state_validity(block.tl, r', r);
		} else {
			lemma_FailurePreservedByBlock(block.tl, r', r);
		}
	}
}

lemma evalWhile_validity(w:whileCond, c:code, n:nat, s:state, r:state)
	requires evalWhile(c, n, s, r);
	decreases c, 1, n;
	ensures valid_state(s) && r.ok ==> valid_state(r);
{
	if valid_state(s) && r.ok && n > 0 {
		var r' :| evalCode(c, s, r') && evalWhile(c, n - 1, r', r);
		code_state_validity(c, s, r');
		evalWhile_validity(w, c, n - 1, r', r);
		assert valid_state(r);
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
            assert true;
        } else if c.Ins256? {
            assert true;
        } else if c.Block? {
            block_state_validity(c.block, s, r);
        } else if c.While? {
            var n:nat :| evalWhile(c.whileBody, n, s, r);
            evalWhile_validity(c.whileCond, c.whileBody, n, s, r);
            assert valid_state(r);
        }
    }
}

lemma va_lemma_empty(s: va_state, r: va_state) returns(r': va_state)
    requires eval_code(Block(va_CNil()), s, r)
    ensures  s.ok ==> r.ok
    ensures  r' == s
    ensures  s.ok ==> r == s
{
    reveal_evalCodeOpaque();
    r' := s;
}

predicate {:opaque} RV_ValidState(s:state)
    ensures RV_ValidState(s) ==> valid_state(s);
{
    valid_state(s)
}

lemma va_lemma_block(b:codes, s0: va_state, r: va_state) returns(r1: va_state, c0:code, b1:codes)
    requires b.va_CCons?
    requires eval_code(Block(b), s0, r)
    ensures  b == va_CCons(c0, b1)
    ensures  eval_code(c0, s0, r1)
		ensures RV_ValidState(s0) && r1.ok ==> RV_ValidState(r1);
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
        r1 := state(r'.regs, r'.mem, r'.pc, r'.ok);
        if RV_ValidState(s0) {
            reveal_RV_ValidState();
            code_state_validity(c0, s0, r1);
        }
        assert eval_code(c0, s0, r1);
    } else {
        // If s0 isn't okay, we can do whatever we want,
        // so we ensure r1.ok is false, and hence eval_code(*, r1, *) is trivially true
        r1 := s0;
    }
}

predicate {:opaque} evalWhileOpaque(w:whileCond, c:code, n:nat, s:state, r:state)
{
    evalWhile(c, n, s, r)
}

predicate evalWhileLax(w:whileCond, c:code, n:nat, s:state, r:state)
{
    s.ok ==> evalWhileOpaque(w, c, n, s, r)
}

predicate va_whileInv(w:whileCond, c:code, n:int, r1: va_state, r2: va_state)
{
    n >= 0 && RV_ValidState(r1) && evalWhileLax(w, c, n, r1, r2)
}

lemma va_lemma_while(w:whileCond, c:code, s: va_state, r: va_state) returns(n:nat, r': va_state)
    // requires va_is_src_reg32(w.r, s);
    // requires va_is_src_imm32(w.c, s);
    requires RV_ValidState(s);
    requires eval_code(While(w, c), s, r)
    ensures  evalWhileLax(w, c, n, r', r)
    //ensures  r'.ok
    ensures s.ok ==> (n == eval_cond(s, w));
    ensures  RV_ValidState(r');
    ensures r' == s
{
    reveal_evalCodeOpaque();
    reveal_RV_ValidState();
    reveal_evalWhileOpaque();
    if s.ok {
        assert evalCode(While(w, c), s, r);
        n := eval_cond(s, w);
    } else {
        n := 0;
    }
    r' := s;
}

lemma va_lemma_whileTrue(w:whileCond, c:code, n:nat, s: va_state, r: va_state) returns(s': va_state, r': va_state)
    // requires va_is_src_reg32(w.r, s) && ValidSourceRegister32(s, w.r);
    // requires va_is_src_imm32(w.c, s);
    requires n > 0
    requires evalWhileLax(w, c, n, s, r)
    ensures  RV_ValidState(s) ==> RV_ValidState(s');
    ensures  evalWhileLax(w, c, n - 1, r', r)
    ensures  eval_code(c, s', r');
    // ensures  BN_ValidState(s) ==> if s.ok then BN_branchRelation(s, s', true) else s' == s;
    ensures  if s.ok && RV_ValidState(s) then
                && s'.ok
                && s == s'
                // && eval_cond(s, w) > 0
             else
                 true; //!r.ok;
{
    reveal_evalCodeOpaque();
    reveal_evalWhileOpaque();
    reveal_RV_ValidState();

    if !s.ok {
        s' := s;
        r' := s;
        return;
    }
    assert evalWhile(c, n, s, r); // TODO: Dafny reveal/opaque issue

    if RV_ValidState(s) {
        var r'':state :| evalCode(c, s, r'') && evalWhile( c, n - 1, r'', r);
        s' := s;
        r' := r'';
        code_state_validity(c, s', r'');
    } else {
        s' := s.(ok := false);
        r' := s.(ok := false);
    }
}

lemma va_lemma_whileFalse(w:whileCond, c:code, s: va_state, r: va_state) returns(r': va_state)
    // requires va_is_src_reg32(w.r, s) && ValidSourceRegister32(s, w.r);
    // requires va_is_src_imm32(w.c, s);
    requires evalWhileLax(w, c, 0, s, r)
    ensures  if s.ok then
                (if RV_ValidState(s) then
                    (r'.ok ==> RV_ValidState(r'))
                //  && BN_branchRelation(s, r', false)
                //  && eval_cond(s, w) == 0
                && s == r
                && r.ok
                 else
                    true)
                  && r' == r
            else
                r' == s; //!r.ok;
{
    reveal_evalCodeOpaque();
    reveal_evalWhileOpaque();
    reveal_RV_ValidState();

    if !s.ok {
        r' := s;
        return;
    }
    r' := r;
}
/*

////////////////////////////////////////////////////////////////////////
//
//  Helper lemmas about control flow
//
////////////////////////////////////////////////////////////////////////


*/
}
