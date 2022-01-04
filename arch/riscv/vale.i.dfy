include "machine.s.dfy"
include "../../std_lib/src/NonlinearArithmetic/Mul.dfy"

module rv_vale {
    import opened integers
    import opened rv_machine

    import bv32_ops
    import bv32_seq
    import Mul

    //  pair/seq

    function fst<T,Q>(t:(T, Q)) : T { t.0 }

    function snd<T,Q>(t:(T, Q)) : Q { t.1 }

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

    function ToNat(xs: seq<uint32>): nat
    {
        bv32_seq.ToNatRight(xs)
    }

    function SeqZero(n: nat): seq<uint32>
    {
        bv32_seq.SeqZero(n)
    }

    function mod(a: int, n: nat): int
        requires n != 0;
    {
        a % n
    }

    // need this for mul

    function va_mul_nat(a: nat, b: nat): nat
    {
        Mul.LemmaMulNonnegativeAuto();
        a * b
    }

    function method uint32_addi(x: uint32, y: bv32_ops.sint): uint32
    {
        bv32_ops.addi(x, y)
    }

    function method uint32_add(x: uint32, y: uint32): uint32
    {
        bv32_ops.add(x, y)
    }

    function method uint32_andi(x: uint32, y: bv32_ops.sint): uint32
    {
        bv32_ops.andi(x, y)
    }

    // otbn state realted

    type va_code = code

    type va_codes = codes

    type va_state = state

    // reg32

    type va_value_reg32 = uint32

    type va_operand_reg32 = reg32_t

    function va_get_reg32_t(r: reg32_t, s: va_state): uint32
    {
        s.read_reg32(r)
    }

    function va_update_reg32_t(r: reg32_t, sM: va_state, sK: va_state): va_state
    {
        var index := reg32_to_index(r);
        sK.(regs := sK.regs[index := sM.regs[index]])
    }

    predicate va_is_src_reg32(r: reg32_t, s: va_state)
    {
        true
    }

    predicate va_is_dst_reg32(r: reg32_t, s: va_state)
    {
        r.index != 0 && r.index != 1
    }

    function va_eval_reg32(s: va_state, r: reg32_t):uint32
    {
        va_get_reg32_t(r, s)
    }

    function va_update_operand_reg32(r: reg32_t, sM: va_state, sK: va_state): va_state
    {
        va_update_reg32_t(r, sM, sK)
    }

    function method va_op_cmp_reg32_t(r: reg32_t) : reg32_t
    {
        r
    }

    // mem

    function va_get_mem(s: va_state): map<int, uint32>
    {
        s.mem
    }

    function va_update_mem(sM: va_state, sK: va_state): va_state
    {
        sK.(mem := sM.mem)
    }

    // ok

    function va_update_ok(sM: va_state, sK: va_state): va_state
    {
        sK.(ok := sM.ok)
    }

    function va_get_ok(s: va_state): bool
    {
        s.ok
    }

    predicate va_state_eq(s0: va_state, s1: va_state)
    {
        // s0 == s1
        && s0.regs == s1.regs
        && s0.mem == s1.mem
        && s0.ok == s1.ok
    }

    // control flow lemmas

    predicate{:opaque} eval_code_opaque(c: code, s0: state, sN: state)
    {
        sN == s0.eval_code(c)
    }

    predicate eval_code_lax(c: code, s: va_state, r: va_state)
    {
        s.ok ==> eval_code_opaque(c, s, r)
    }

    predicate {:opaque} valid_state_opaque(s: va_state)
        ensures valid_state_opaque(s) ==> valid_state(s);
    {
        && s.ok
        && valid_state(s)
    }

    function method va_CNil(): codes { CNil }

    predicate cHeadIs(b: codes, c: code) { b.va_CCons? && b.hd == c }

    predicate cTailIs(b: codes, t: codes) { b.va_CCons? && b.tl == t }

    predicate va_require(
        complete_block: codes,
        head_code: code,
        s0: va_state,
        sN: va_state)
    {
        && cHeadIs(complete_block, head_code)
        && eval_code_lax(Block(complete_block), s0, sN)
        && valid_state_opaque(s0)
    }

    // Weaker form of eval_code that we can actually ensure generically in instructions
    predicate eval_weak(c: code, s: va_state, r: va_state)
    {
        s.ok && r.ok ==> eval_code_opaque(c, s, r)
    }

    predicate va_ensure(b0: codes, b1: codes, s0: va_state, s1: va_state, sN: va_state)
    {
        && cTailIs(b0, b1)
        && eval_weak(b0.hd, s0, s1)
        && eval_code_lax(Block(b1), s1, sN)
        && valid_state_opaque(s1)
    }

    lemma va_ins_lemma(b0:code, s0: va_state)
    {
    }

    function method va_const_cmp(n: uint32):uint32 { n }
    function method va_coerce_reg32_to_cmp(r: reg32_t): reg32_t { r }

    function method va_cmp_eq(r1:reg32_t, r2:reg32_t):cond { Cmp(Eq, r1, r2) }
    function method va_cmp_ne(r1:reg32_t, r2:reg32_t):cond { Cmp(Ne, r1, r2) }
    function method va_cmp_le(r1:reg32_t, r2:reg32_t):cond { Cmp(Le, r1, r2) }
    function method va_cmp_ge(r1:reg32_t, r2:reg32_t):cond { Cmp(Ge, r1, r2) }
    function method va_cmp_lt(r1:reg32_t, r2:reg32_t):cond { Cmp(Lt, r1, r2) }
    function method va_cmp_gt(r1:reg32_t, r2:reg32_t):cond { Cmp(Gt, r1, r2) }

    function method va_op_reg32_reg32_t(r: reg32_t): reg32_t { r }

    function method va_Block(block:codes): code { Block(block) }
    function method va_While(wcond: cond, wcode: code): code { While(wcond, wcode) }
    function method va_Function(name: string, body: codes): code { Function(name, body) }
    function method va_IfElse(ifb: cond, ift:code, iff:code):code { IfElse(ifb, ift, iff) }

    function method va_get_block(c: code): codes requires c.Block? || c.Function? { 
        if c.Block? then c.block else c.functionBody }
    function method va_get_whileCond(c: code): cond requires c.While? {c.whileCond }
    function method va_get_whileBody(c: code): code requires c.While? { c.whileBody }
    function method va_get_ifCond(c:code):cond requires c.IfElse? { c.ifCond }
    function method va_get_ifTrue(c:code):code requires c.IfElse? { c.ifTrue }
    function method va_get_ifFalse(c:code):code requires c.IfElse? { c.ifFalse }


    lemma lemma_FailurePreservedByBlock(block: codes, s: state, r: state)
        requires r == s.eval_block(block);
        ensures !s.ok ==> !r.ok;
        decreases block;
    {
        if !block.CNil? {
            var r' :| r' == s.eval_code(block.hd) && r == r'.eval_block(block.tl);
            lemma_FailurePreservedByCode(block.hd, s, r');
            lemma_FailurePreservedByBlock(block.tl, r', r);
        }
    }

    lemma lemma_FailurePreservedByCode(c: code, s: state, r: state)
        requires r == s.eval_code(c);
        ensures !s.ok ==> !r.ok;
    {
        match c {
            case Block(b) => {
                lemma_FailurePreservedByBlock(b, s, r);
            }
            case Function(_, b) => {
                lemma_FailurePreservedByBlock(b, s, r);
            }
            case _ => {
                var r' :| r' == s.eval_code(c);
            }
        }
    }

    lemma block_state_validity(block: codes, s: state, r: state)
        requires r == s.eval_block(block);
        requires valid_state(s);
        decreases block, 0;
        ensures r.ok ==> valid_state(r);
    {
        if block.va_CCons? {
            var r':state :| r' == s.eval_code(block.hd) && r == r'.eval_block(block.tl);
            code_state_validity(block.hd, s, r');
            if r'.ok {
                block_state_validity(block.tl, r', r);
            } else {
                lemma_FailurePreservedByBlock(block.tl, r', r);
            }
        }
    }

    lemma eval_while_validity(w:cond, c:code, n:nat, s:state, r:state)
        requires r == s.eval_while(c, n);
        decreases c, 1, n;
        ensures valid_state(s) && r.ok ==> valid_state(r);
    {
        if valid_state(s) && r.ok && n > 0 {
            var r' :| r' == s.eval_code(c) && r == r'.eval_while(c, n - 1);
            code_state_validity(c, s, r');
            eval_while_validity(w, c, n - 1, r', r);
            assert valid_state(r);
        }
    }

    lemma code_state_validity(c:code, s:state, r:state)
        requires r == s.eval_code(c);
        requires valid_state(s);
        decreases c, 0;
        ensures  r.ok ==> valid_state(r);
    {
        if r.ok {
            if c.Ins32? {
                assert true;
            } else if c.Block? {
                block_state_validity(c.block, s, r);
            } else if c.IfElse? {
                if s.eval_cmp(c.cond) {
                    code_state_validity(c.ifTrue, s, r);
                } else {
                    code_state_validity(c.ifFalse, s, r);
                }
            } else if c.While? {
                var n:nat :| r == s.eval_while(c.whileBody, n);
                eval_while_validity(c.whileCond, c.whileBody, n, s, r);
                assert valid_state(r);
            } else if c.Comment? {
            }
        } 
    }

    lemma va_lemma_empty(s: va_state, r: va_state) returns (r': va_state)
        requires eval_code_lax(Block(va_CNil()), s, r)
        ensures  s.ok ==> r.ok
        ensures  r' == s
        ensures  s.ok ==> r == s
    {
        reveal_eval_code_opaque();
        r' := s;
    }

    lemma va_lemma_block(
        complete_block: codes,
        s0: va_state,
        r: va_state)
    returns(r1: va_state, current:code, rest:codes)

        requires complete_block.va_CCons?
        requires eval_code_lax(Block(complete_block), s0, r)

        ensures complete_block == va_CCons(current, rest)
        ensures eval_code_lax(current, s0, r1)
        ensures current.Function? ==>
            eval_code_lax(Block(current.functionBody), s0, r1)
        ensures eval_code_lax(Block(rest), r1, r)
    {
        reveal_eval_code_opaque();
        current := complete_block.hd;
        rest := complete_block.tl;
        if s0.ok {
            assert r == s0.eval_block(complete_block);
            var r':state :| r' == s0.eval_code(complete_block.hd) && r == r'.eval_block(complete_block.tl);
            current := complete_block.hd;
            rest := complete_block.tl;
            r1 := r';
            if valid_state_opaque(s0) {
                reveal_valid_state_opaque();
                code_state_validity(current, s0, r1);
            }
            assert eval_code_lax(current, s0, r1);
        } else {
            // If s0 isn't okay, we can do whatever we want,
            // so we ensure r1.ok is false, and hence eval_code_lax(*, r1, *) is trivially true
            r1 := s0;
        }
    }

    predicate {:opaque} eval_while_opaque(w: cond, c: code, n: nat, s: state, r: state)
    {
        r == s.eval_while(c, n)
    }

    predicate eval_while_lax(w: cond, c: code, n: nat, s: state, r: state)
    {
        s.ok ==> eval_while_opaque(w, c, n, s, r)
    }

    predicate va_whileInv(w:cond, c:code, n:int, r1: va_state, r2: va_state)
    {
        n >= 0 && valid_state_opaque(r1) && eval_while_lax(w, c, n, r1, r2)
    }

    lemma va_lemma_while(w: cond, c: code, s: va_state, r: va_state) returns(n: nat, r': va_state)
        requires valid_state_opaque(s);
        requires eval_code_lax(While(w, c), s, r)
        ensures  eval_while_lax(w, c, n, r', r)
        ensures s.ok ==> (n == s.eval_cond(w));
        ensures valid_state_opaque(r');
        ensures r' == s
    {
        reveal_eval_code_opaque();
        reveal_valid_state_opaque();
        reveal_eval_while_opaque();
        if s.ok {
            assert r == s.eval_code(While(w, c));
            n := s.eval_cond(w);
        } else {
            n := 0;
        }
        r' := s;
    }

    lemma va_lemma_whileTrue(w: cond, c: code, n: nat, s: va_state, r: va_state) returns(s': va_state, r': va_state)
        requires n > 0
        requires eval_while_lax(w, c, n, s, r)
        ensures  valid_state_opaque(s) ==> valid_state_opaque(s');
        ensures  eval_while_lax(w, c, n - 1, r', r)
        ensures  eval_code_lax(c, s', r');
        ensures  if s.ok && valid_state_opaque(s) then
                    && s'.ok
                    && s == s'
                else
                    true; //!r.ok;
    {
        reveal_eval_code_opaque();
        reveal_eval_while_opaque();
        reveal_valid_state_opaque();

        if !s.ok {
            s' := s;
            r' := s;
            return;
        }
        assert r == s.eval_while(c, n); 

        if valid_state_opaque(s) {
            var r'':state :| r'' == s.eval_code(c) && r == r''.eval_while(c, n - 1);
            s' := s;
            r' := r'';
            code_state_validity(c, s', r'');
        } else {
            s' := s.(ok := false);
            r' := s.(ok := false);
        }
    }

    lemma va_lemma_whileFalse(w: cond, c: code, s: va_state, r: va_state) returns (r': va_state)
        requires eval_while_lax(w, c, 0, s, r)
        ensures  if s.ok then
                    (if valid_state_opaque(s) then
                        (r'.ok ==> valid_state_opaque(r'))
                    && s == r
                    && r.ok
                    else
                        true)
                    && r' == r
                else
                    r' == s; //!r.ok;
    {
        reveal_eval_code_opaque();
        reveal_eval_while_opaque();
        reveal_valid_state_opaque();

        if !s.ok {
            r' := s;
            return;
        }
        r' := r;
    }

    lemma va_lemma_ifElse(ifb: cond, ct:code, cf:code, s:va_state, r:va_state) returns(cond:bool, s':va_state)
    requires valid_state_opaque(s);
    requires eval_code_lax(IfElse(ifb, ct, cf), s, r)
    ensures  if s.ok then
                && s'.ok
                && valid_state_opaque(s')
                && cond == s.eval_cmp(ifb) 
                && s' == s
                && (if cond then eval_code_lax(ct, s', r) else eval_code_lax(cf, s', r))
            else
                true
    {
        reveal_eval_code_opaque();
        reveal_valid_state_opaque();
        cond := s.eval_cmp(ifb);
        if s.ok {
            assert r == s.eval_code(IfElse(ifb, ct, cf));
            if cond {
                code_state_validity(ct, s, r);
            } else {
                code_state_validity(cf, s, r);
            }
        }
        s' := s;
    }
}
