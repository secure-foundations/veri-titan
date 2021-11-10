include "abstraction.i.dfy"
include "../../std_lib/src/NonlinearArithmetic/Mul.dfy"

module ot_vale {
    // import opened bv_ops
    import opened integers
    import opened ot_machine
    import opened ot_abstraction
    import bv32_ops
    import bv256_seq

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

    function ToNat(xs: seq<uint256>): nat
    {
        bv256_seq.ToNatRight(xs)
    }

    function SeqZero(n: nat): seq<uint256>
    {
        bv256_seq.SeqZero(n)
    }

    function mod(a: int, n: nat): int
        requires n != 0;
    {
        a % n
    }

    lemma xor_clear_lemma(x: uint256)
        ensures bv256_ops.xor(x, x) == 0;

    // need this for mul

    function va_mul_nat(a: nat, b: nat): nat
    {
        Mul.LemmaMulNonnegativeAuto();
        a * b
    }

    function method bool_to_uint1(b: bool): uint1
    {
        bv256_ops.bool_to_uint1(b)
    }

    function method uint32_addi(x: uint32, y: bv32_ops.sint): uint32
    {
        bv32_ops.addi(x, y)
    }

    function method uint32_add(x: uint32, y: uint32): uint32
    {
        bv32_ops.add(x, y)
    }

    // otbn state realted

    datatype gstate = gstate(ms: state, heap: heap_t)

    type va_code = code

    type va_codes = codes

    type va_state = gstate

    // reg32

    type va_value_reg32 = uint32

    type va_operand_reg32 = reg32_t

    function va_get_reg32_t(r: reg32_t, s: va_state): uint32
    {
        s.ms.read_reg32(r)
    }

    function va_update_reg32_t(r: reg32_t, sM: va_state, sK: va_state): va_state
    {
        var temp := sM.ms.read_reg32(r);
        sK.(ms := sK.ms.write_reg32(r, temp))
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

    // reg256

    type va_value_reg256 = uint256

    type va_operand_reg256 = reg256_t

    function va_get_reg256_t(r :reg256_t, s: va_state): uint256
    {
        s.ms.read_reg256(r)
    }

    function va_update_reg256_t(r: reg256_t, sM: va_state, sK: va_state): va_state
    {
        var temp := sM.ms.read_reg256(r);
        sK.(ms := sK.ms.write_reg256(r, temp))
    }

    predicate va_is_src_reg256(r :reg256_t, s: va_state)
    {
        r.WDR?
    }

    predicate va_is_dst_reg256(r :reg256_t, s: va_state)
    {
        r.WDR?
    }

    function va_update_operand_reg256(r :reg256_t, sM: va_state, sK: va_state): va_state
    {
        va_update_reg256_t(r, sM, sK)
    }

    function va_eval_reg256(s: va_state, r :reg256_t): uint256
    {
        va_get_reg256_t(r, s)
    }

    // fgroups

    function va_get_fgroups(s: va_state): fgroups_t
    {
        s.ms.fgroups
    }

    function va_update_fgroups(sM: va_state, sK: va_state): va_state
    {
        var temp := sM.ms.fgroups;
        sK.(ms := sK.ms.(fgroups := temp))
    }

    // wdrs

    function va_get_wdrs(s: va_state): seq<uint256>
    {
        s.ms.wdrs
    }

    function va_update_wdrs(sM: va_state, sK: va_state): va_state
    {
        var temp := sM.ms.wdrs;
        sK.(ms := sK.ms.(wdrs := temp))
    }

    // mem

    function va_get_mem(s: va_state): map<int, uint32>
    {
        s.ms.mem
    }

    function va_update_mem(sM: va_state, sK: va_state): va_state
    {
        var temp := sM.ms.mem;
        sK.(ms := sK.ms.(mem := temp))
    }

    // heap

    function va_get_heap(s: va_state): heap_t
    {
        s.heap
    }

    function va_update_heap(sM: va_state, sK: va_state): va_state
    {
        sK.(heap := sM.heap)
    }

    lemma sw_correct(gs: gstate, grs2: reg32_t,
        offset: int12, grs1: reg32_t, write_ptr: uint32)
        returns (new_heap: heap_t)

        requires valid_state_opaque(gs)
        requires write_ptr == bv32_ops.addi(gs.ms.read_reg32(grs1), offset);
        requires xword_ptr_valid(gs.heap, write_ptr);

        ensures
            var r := gs.ms.eval_SW(grs2, offset, grs1);
            var gr := gstate(r, new_heap);
            var value := gs.ms.read_reg32(grs2);
            && valid_state_opaque(gr)
            && xword_ptr_valid(gr.heap, write_ptr)
            && heap_read_xword(gr.heap, write_ptr) == value
            && new_heap == heap_write_xword(gs.heap, write_ptr, value)
    {
        reveal valid_state_opaque();

        var value := gs.ms.read_reg32(grs2);
        new_heap := heap_write_xword(gs.heap, write_ptr, value);

        write_xword_preverses_mem_equiv(gs.heap, new_heap,
            gs.ms.mem, gs.ms.mem[write_ptr := value],
            write_ptr, value);
    }

    lemma bn_lid_correct(gs: gstate,
        grd: reg32_t, grd_inc: bool,
        offset: int10, grs: reg32_t, grs_inc: bool,
        addr: uint32, iter: iter_t)
        returns (new_iter: iter_t)

        requires valid_state_opaque(gs)
        // note this is overly restricting 
        requires offset == 0
        requires grd.index != grs.index
            && grd.index != 0
            && grd.index != 1
            && grs.index != 0
            && grs.index != 1
        requires gs.ms.read_reg32(grd) <= 31
        requires addr == wwrod_offset_ptr(gs.ms.read_reg32(grs), offset)
        requires iter_safe(iter, gs.heap, addr)

        ensures 
            var r := gs.ms.eval_BN_LID(grd, grd_inc, offset, grs, grs_inc);
            var gr := gstate(r, gs.heap);
            && valid_state_opaque(gr)
            // the resulting gerenal registers
            && gr.ms.read_reg32(grd) == (gs.ms.read_reg32(grd) + if grd_inc then 1 else 0)
            && gr.ms.read_reg32(grs) == (gs.ms.read_reg32(grs) + if grs_inc then 32 else 0)
            // new_iter still reflects the memory
            && new_iter == bn_lid_next_iter(iter, grs_inc)
            && var addr := wwrod_offset_ptr(gr.ms.read_reg32(grs), offset);
            && iter_inv(new_iter, gr.heap, addr)
            // the resulting wide register
            && gr.ms.wdrs[gs.ms.read_reg32(grd)] == new_iter.buff[iter.index]
    {
        reveal valid_state_opaque();
        new_iter := bn_lid_next_iter(iter, grs_inc);
        var r := gs.ms.eval_BN_LID(grd, grd_inc, offset, grs, grs_inc);
    }

    lemma bn_sid_correct(gs: gstate, 
        grs2: reg32_t, grs2_inc: bool,
        offset: int10, grs1: reg32_t, grs1_inc: bool,
        value: uint256, addr: uint32, iter: iter_t)
    returns (result: (heap_t, iter_t))

        requires valid_state_opaque(gs)
        // note this is overly restricting 
        requires offset == 0
        requires grs1.index != grs2.index
            && grs1.index != 0
            && grs1.index != 1
            && grs2.index != 0
            && grs2.index != 1
        requires
            var s := gs.ms;
            && s.read_reg32(grs2) <= 31
            && addr == wwrod_offset_ptr(s.read_reg32(grs1), offset)
            && value == s.read_reg256(WDR(s.read_reg32(grs2)))
            && iter_safe(iter, gs.heap, addr)

        ensures
            var (new_h, new_iter) := result;
            var s := gs.ms;
            var r := s.eval_BN_SID(grs2, grs2_inc, offset, grs1, grs1_inc);
            var gr := gstate(r, new_h);
            && valid_state_opaque(gr)
            // the resulting gerenal registers
            && r.read_reg32(grs2) == (s.read_reg32(grs2) + if grs2_inc then 1 else 0)
            && r.read_reg32(grs1) == (s.read_reg32(grs1) + if grs1_inc then 32 else 0)
            // new_iter still reflects the memory
            && new_iter == bn_sid_next_iter(iter, value, grs1_inc)
            && var addr := wwrod_offset_ptr(r.read_reg32(grs1), offset);
            && iter_inv(new_iter, new_h, addr)
            && gr.heap == gs.heap[iter.base_ptr := WBUFF(new_iter.buff)]
    {
        reveal valid_state_opaque();
        var r := gs.ms.eval_BN_SID(grs2, grs2_inc, offset, grs1, grs1_inc);
        var heap' := heap_write_wword(gs.heap, iter, addr, value);
        write_wword_preverses_mem_equiv(
            gs.heap, heap', iter,
            gs.ms.mem, r.mem, addr, value);
        var iter' := bn_sid_next_iter(iter, value, grs1_inc);
        return (heap', iter');
    }

    // ok

    function va_update_ok(sM: va_state, sK: va_state): va_state
    {
        var temp := sM.ms.ok;
        sK.(ms := sK.ms.(ok := temp))
    }

    function va_get_ok(s: va_state): bool
    {
        s.ms.ok
    }

    predicate va_state_eq(s0: va_state, s1: va_state)
    {
        // s0 == s1
        && s0.heap == s1.heap
        && s0.ms == s1.ms
        // && s0.ms.gprs == s1.ms.gprs
        // && s0.ms.wdrs == s1.ms.wdrs
        // && s0.ms.wmod == s1.ms.wmod
        // && s0.ms.wrnd == s1.ms.wrnd
        // && s0.ms.wacc == s1.ms.wacc
        // && s0.ms.fgroups == s1.ms.fgroups
        // && s0.ms.mem == s1.ms.mem
        // && s0.ms.wmem == s1.ms.wmem
        // && s0.ms.ok == s1.ms.ok
    }

    // control flow lemmas

    predicate{:opaque} eval_code_opaque(c: code, s0: state, sN: state)
    {
        sN == s0.eval_code(c)
    }

    predicate eval_code_lax(c: code, s: va_state, r: va_state)
    {
        s.ms.ok ==> eval_code_opaque(c, s.ms, r.ms)
    }

    predicate {:opaque} valid_state_opaque(s: va_state)
        ensures valid_state_opaque(s) ==> valid_state(s.ms);
    {
        && s.ms.ok
        && mem_equiv(s.heap, s.ms.mem)
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
        s.ms.ok && r.ms.ok ==> eval_code_opaque(c, s.ms, r.ms)
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

    function method va_cmp_LoopImm(u:uint32): whileCond { ImmCond(u) }
    function method va_cmp_Loop(r: reg32_t): whileCond { RegCond(r) }

    function method va_op_reg32_reg32_t(r: reg32_t): reg32_t { r }
    function method va_op_reg256_reg256_t(r :reg256_t): reg256_t { r }

    function method va_Block(block:codes): code { Block(block) }
    function method va_While(wcond: whileCond, wcode: code): code { While(wcond, wcode) }
    function method va_Function(name: string, body: codes): code { Function(name, body) }

    function method va_get_block(c: code): codes requires c.Block? || c.Function? { 
        if c.Block? then c.block else c.functionBody }
    function method va_get_whileCond(c: code): whileCond requires c.While? {c.whileCond }
    function method va_get_whileBody(c: code): code requires c.While? { c.whileBody }
    
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
            case While(c, b) => {
                var n :| r == s.eval_while(b, n);
            }
            case Ins256(i) => {
                var r' :| r' == s.eval_code(c);
            }
            case Ins32(i) => {
                var r' :| r' == s.eval_code(c);
            }
            case Comment(com) => {
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

    lemma eval_while_validity(w:whileCond, c:code, n:nat, s:state, r:state)
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
            } else if c.Ins256? {
                assert true;
            } else if c.Block? {
                block_state_validity(c.block, s, r);
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
        ensures  s.ms.ok ==> r.ms.ok
        ensures  r' == s
        ensures  s.ms.ok ==> r.ms == s.ms
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
        if s0.ms.ok {
            assert r.ms == s0.ms.eval_block(complete_block);
            var r':state :| r' == s0.ms.eval_code(complete_block.hd) && r.ms == r'.eval_block(complete_block.tl);
            current := complete_block.hd;
            rest := complete_block.tl;
            r1 := gstate(r', s0.heap);
            // r1 := gstate(r'.gprs, r'.wdrs, r'.wmod, r'.wrnd, r'.wacc, r'.fgroups, r'.mem, r'.wmem, r'.ok);
            if valid_state_opaque(s0) {
                reveal_valid_state_opaque();
                code_state_validity(current, s0.ms, r1.ms);
            }
            assert eval_code_lax(current, s0, r1);
        } else {
            // If s0 isn't okay, we can do whatever we want,
            // so we ensure r1.ok is false, and hence eval_code_lax(*, r1, *) is trivially true
            r1 := s0;
        }
    }

    predicate {:opaque} eval_while_opaque(w: whileCond, c: code, n: nat, s: state, r: state)
    {
        r == s.eval_while(c, n)
    }

    predicate eval_while_lax(w: whileCond, c: code, n: nat, s: state, r: state)
    {
        s.ok ==> eval_while_opaque(w, c, n, s, r)
    }

    predicate va_whileInv(w:whileCond, c:code, n:int, r1: va_state, r2: va_state)
    {
        n >= 0 && valid_state_opaque(r1) && eval_while_lax(w, c, n, r1.ms, r2.ms)
    }

    lemma va_lemma_while(w: whileCond, c: code, s: va_state, r: va_state) returns(n: nat, r': va_state)
        // requires va_is_src_reg32(w.r, s);
        // requires va_is_src_imm32(w.c, s);
        requires valid_state_opaque(s);
        requires eval_code_lax(While(w, c), s, r)
        ensures  eval_while_lax(w, c, n, r'.ms, r.ms)
        //ensures  r'.ok
        ensures s.ms.ok ==> (n == s.ms.eval_cond(w));
        ensures valid_state_opaque(r');
        ensures r' == s
    {
        reveal_eval_code_opaque();
        reveal_valid_state_opaque();
        reveal_eval_while_opaque();
        if s.ms.ok {
            assert r.ms == s.ms.eval_code(While(w, c));
            n := s.ms.eval_cond(w);
        } else {
            n := 0;
        }
        r' := s;
    }

    lemma va_lemma_whileTrue(w: whileCond, c: code, n: nat, s: va_state, r: va_state) returns(s': va_state, r': va_state)
        // requires va_is_src_reg32(w.r, s) && ValidSourceRegister32(s, w.r);
        // requires va_is_src_imm32(w.c, s);
        requires n > 0
        requires eval_while_lax(w, c, n, s.ms, r.ms)
        ensures  valid_state_opaque(s) ==> valid_state_opaque(s');
        ensures  eval_while_lax(w, c, n - 1, r'.ms, r.ms)
        ensures  eval_code_lax(c, s', r');
        // ensures  valid_state_opaque(s) ==> if s.ok then BN_branchRelation(s, s', true) else s' == s;
        ensures  if s.ms.ok && valid_state_opaque(s) then
                    && s'.ms.ok
                    && s == s'

                    && (s.heap == s'.heap == r'.heap)
                    // && eval_cond(s, w) > 0
                else
                    true; //!r.ok;
    {
        reveal_eval_code_opaque();
        reveal_eval_while_opaque();
        reveal_valid_state_opaque();

        if !s.ms.ok {
            s' := s;
            r' := s;
            return;
        }
        assert r.ms == s.ms.eval_while(c, n); 

        if valid_state_opaque(s) {
            var r'':state :| r'' == s.ms.eval_code(c) && r.ms == r''.eval_while(c, n - 1);
            s' := s;
            r' := gstate(r'', s.heap);
            code_state_validity(c, s'.ms, r'');
        } else {
            s' := s.(ms := s.ms.(ok := false));
            r' := s.(ms := s.ms.(ok := false));
        }
    }

    lemma va_lemma_whileFalse(w: whileCond, c: code, s: va_state, r: va_state) returns (r': va_state)
        requires eval_while_lax(w, c, 0, s.ms, r.ms)
        ensures  if s.ms.ok then
                    (if valid_state_opaque(s) then
                        (r'.ms.ok ==> valid_state_opaque(r'))
                    //  && BN_branchRelation(s, r', false)
                    //  && eval_cond(s, w) == 0
                    && s.ms == r.ms
                    && r.ms.ok
                    else
                        true)
                    && r'.ms == r.ms
                    && r'.heap == s.heap
                else
                    r' == s; //!r.ok;
    {
        reveal_eval_code_opaque();
        reveal_eval_while_opaque();
        reveal_valid_state_opaque();

        if !s.ms.ok {
            r' := s;
            return;
        }
        r' := r.(heap := s.heap);
    }
}
