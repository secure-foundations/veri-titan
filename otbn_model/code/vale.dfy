include "../spec/rsa_ops.dfy"

module vt_vale {
    import opened vt_ops
    import opened bv_ops
    import opened rsa_ops
    import opened congruences
    import opened vt_consts

    type va_code = code
    type va_codes = codes
    type va_state = state

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

    function mod_add(a: nat, b: nat, m: nat): nat 
        requires a < m && b < m;
    {
        if a + b > m then a + b - m else a + b
    }

    function va_get_ok(s: va_state): bool
    {
        s.ok
    }

    function va_get_reg32_t(r : reg32_t, s: va_state): uint32
    {
        s.read_reg32(r)
    }

    function va_get_reg256_t(r :reg256_t, s: va_state): uint256
    {
        s.read_reg256(r)
    }

    function va_eval_reg256(s: va_state, r :reg256_t): uint256
    {
        s.read_reg256(r)
    }

    function va_get_fgroups(s: va_state): fgroups_t
    {
        s.fgroups
    }

    function va_get_xmem(s: va_state): map<int, uint32>
    {
        s.xmem
    }

    function va_update_xmem(sM: va_state, sK: va_state): va_state
    {
        sK.(xmem := sM.xmem)
    }

    function va_get_wmem(s: va_state): wmem_t
    {
        s.wmem
    }

    function va_update_wmem(sM: va_state, sK: va_state): va_state
    {
        sK.(wmem := sM.wmem)
    }

    function va_get_wdrs(s: va_state): seq<uint256>
    {
        s.wdrs
    }

    function va_update_wdrs(sM: va_state, sK: va_state): va_state
    {
        sK.(wdrs := sM.wdrs)
    }

    function va_update_ok(sM: va_state, sK: va_state): va_state
    {
        sK.(ok := sM.ok)
    }

    function va_update_reg32_t(r: reg32_t, sM: va_state, sK: va_state): va_state
    {
        var index := r.index;
        sK.write_reg32(r, sM.read_reg32(r))
        // sK.(gprs := sK.gprs[index := sM.gprs[index]])
    }

    function va_update_reg256_t(r :reg256_t, sM: va_state, sK: va_state): va_state
    {
        match r {
            case WDR(index) => sK.(wdrs := sK.wdrs[index := sM.wdrs[index]])
            case WMOD =>  sK.(wmod := sM.wmod)
            case WRND => sK.(wrnd := sM.wrnd)
            case WACC => sK.(wacc := sM.wacc)
        }
    }

    function va_update_fgroups(sM: va_state, sK: va_state): va_state
    {
        sK.(fgroups := sM.fgroups)
    }

    type va_operand_imm32 = uint32
    predicate va_is_src_imm32(v:uint32, s: va_state) { true }
    function va_eval_imm32(s: va_state, v:uint32):uint32 { v }
    function method va_const_imm32(n:uint32):uint32 { n }

    function va_mul_nat(a: nat, b: nat): nat
    {
        a * b
    }

    // reg32

    type va_value_reg32 = uint32

    type va_operand_reg32 = reg32_t

    predicate va_is_src_reg32(r: reg32_t, s: va_state)
    {
        true
    }

    predicate va_is_dst_reg32(r: reg32_t, s: va_state)
    {
        true
    }

    function va_eval_reg32(s: va_state, r : reg32_t):uint32
    {
        s.read_reg32(r)
    }

    function va_update_operand_reg32(r: reg32_t, sM: va_state, sK: va_state): va_state
    {
        va_update_reg32_t(r, sM, sK)
    }

    function method va_op_cmp_reg32_t(r : reg32_t)  : reg32_t
    {
        r
    }

    // reg256

    type va_value_reg256 = uint256

    type va_operand_reg256 = reg256_t

    predicate va_is_src_reg256(r :reg256_t, s: va_state)
    {
        true
    }

    predicate va_is_dst_reg256(r :reg256_t, s: va_state)
    {
        !r.WRND?
    }

    function va_read_reg256(s: va_state, r :reg256_t):uint256
        requires va_is_src_reg256(r, s);
    {
        s.read_reg256(r)
    }

    function va_update_operand_reg256(r :reg256_t, sM: va_state, sK: va_state): va_state
    {
        va_update_reg256_t(r, sM, sK)
    }

    predicate va_state_eq(s0: va_state, s1: va_state)
    {
        // s0 == s1
        && s0.gprs == s1.gprs
        && s0.wdrs == s1.wdrs
        && s0.fgroups == s1.fgroups

        && s0.wmod == s1.wmod
        && s0.wrnd == s1.wrnd
        && s0.wacc == s1.wacc

        && s0.xmem == s1.xmem
        && s0.wmem == s1.wmem
        
        && s0.ok == s1.ok
    }

    predicate{:opaque} eval_code_opaque(c:code, s0:state, sN:state)
    {
        eval_code(c, s0, sN)
    }

    predicate eval_code_lax(c:code, s:state, r:state)
    {
        s.ok ==> eval_code_opaque(c, s, r)
    }

    function method va_CNil():codes { CNil }
    predicate cHeadIs(b:codes, c:code) { b.va_CCons? && b.hd == c }
    predicate cTailIs(b:codes, t:codes) { b.va_CCons? && b.tl == t }

    predicate va_require(b0:codes, c1:code, s0: va_state, sN: va_state)
    {
        && cHeadIs(b0, c1)
        && eval_code_lax(Block(b0), s0, sN)
        && valid_state_opaque(s0)
    }

    // Weaker form of eval_code that we can actually ensure generically in instructions
    predicate eval_weak(c:code, s:state, r:state)
    {
        s.ok && r.ok ==> eval_code_opaque(c, s, r)
    }

    predicate va_ensure(b0:codes, b1:codes, s0: va_state, s1: va_state, sN: va_state)
    {
        && cTailIs(b0, b1)
        && eval_weak(b0.hd, s0, s1)
        && eval_code_lax(Block(b1), s1, sN)
        && valid_state_opaque(s1)
    }

    lemma va_ins_lemma(b0:code, s0: va_state)
    {
    }

    function method va_const_cmp(n:uint32):uint32 { n }
    function method va_coerce_reg32_to_cmp(r: reg32_t): reg32_t { r }

    function method va_cmp_LoopImm(u:uint32):whileCond { ImmCond(u) }
    function method va_cmp_Loop(r: reg32_t):whileCond { RegCond(r) }

    function method va_op_reg32_reg32_t(r: reg32_t): reg32_t { r }
    function method va_op_reg256_reg256_t(r :reg256_t) :reg256_t { r }
    function method va_Block(block:codes):code { Block(block) }
    function method va_While(wcond:whileCond, wcode:code):code { While(wcond, wcode) }

    function method va_get_block(c:code):codes requires c.Block? { c.block }
    function method va_get_whileCond(c:code):whileCond requires c.While? {c.whileCond }
    function method va_get_whileBody(c:code):code requires c.While? { c.whileBody }

    lemma lemma_FailurePreservedByBlock(block:codes, s:state, r:state)
        requires eval_block(block, s, r);
        ensures !s.ok ==> !r.ok;
        decreases block;
    {
        if !block.CNil? {
            var r' :| eval_code(block.hd, s, r') && eval_block(block.tl, r', r);
            lemma_FailurePreservedByCode(block.hd, s, r');
            lemma_FailurePreservedByBlock(block.tl, r', r);
        }
    }


    lemma lemma_FailurePreservedByCode(c:code, s:state, r:state)
        requires eval_code(c, s, r);
        ensures !s.ok ==> !r.ok;
    {
        match c {
            case Block(b) => {
                lemma_FailurePreservedByBlock(b, s, r);
            }
            case While(c, b) => {
                var n :| eval_while(b, n, s, r);
            }
            case Ins256(i) => {
                var r' :| eval_code(c, s, r');
            }
            case Ins32(i) => {
                var r' :| eval_code(c, s, r');
            }
            case Comment(com) => {
                var r' :| eval_code(c, s, r');
            }
        }
    }

    lemma block_state_validity(block:codes, s:state, r:state)
        requires eval_block(block, s, r);
        requires valid_state(s);
        decreases block, 0;
        ensures r.ok ==> valid_state(r);
    {
        if block.va_CCons? {
            var r':state :| eval_code(block.hd, s, r') && eval_block(block.tl, r', r);
            code_state_validity(block.hd, s, r');
            if r'.ok {
                block_state_validity(block.tl, r', r);
            } else {
                lemma_FailurePreservedByBlock(block.tl, r', r);
            }
        }
    }

    lemma eval_while_validity(w:whileCond, c:code, n:nat, s:state, r:state)
        requires eval_while(c, n, s, r);
        decreases c, 1, n;
        ensures valid_state(s) && r.ok ==> valid_state(r);
    {
        if valid_state(s) && r.ok && n > 0 {
            var r' :| eval_code(c, s, r') && eval_while(c, n - 1, r', r);
            code_state_validity(c, s, r');
            eval_while_validity(w, c, n - 1, r', r);
            assert valid_state(r);
        }
    }

    lemma code_state_validity(c:code, s:state, r:state)
        requires eval_code(c, s, r);
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
                var n:nat :| eval_while(c.whileBody, n, s, r);
                eval_while_validity(c.whileCond, c.whileBody, n, s, r);
                assert valid_state(r);
            } else if c.Comment? {
            }
        } 
    }

    lemma va_lemma_empty(s: va_state, r: va_state) returns(r': va_state)
        requires eval_code_lax(Block(va_CNil()), s, r)
        ensures  s.ok ==> r.ok
        ensures  r' == s
        ensures  s.ok ==> r == s
    {
        reveal_eval_code_opaque();
        r' := s;
    }

    predicate {:opaque} valid_state_opaque(s:state)
        ensures valid_state_opaque(s) ==> valid_state(s);
    {
        valid_state(s)
    }

    lemma va_lemma_block(b:codes, s0: va_state, r: va_state) returns(r1: va_state, c0:code, b1:codes)
        requires b.va_CCons?
        requires eval_code_lax(Block(b), s0, r)
        ensures  b == va_CCons(c0, b1)
        ensures  eval_code_lax(c0, s0, r1)
            ensures valid_state_opaque(s0) && r1.ok ==> valid_state_opaque(r1);
        ensures  eval_code_lax(Block(b1), r1, r)
    {
        reveal_eval_code_opaque();
        c0 := b.hd;
        b1 := b.tl;
        if s0.ok {
            assert eval_block(b, s0, r);
            var r':state :| eval_code(b.hd, s0, r') && eval_block(b.tl, r', r);
            c0 := b.hd;
            b1 := b.tl;
            r1 := state(r'.gprs, r'.wdrs, r'.wmod, r'.wrnd, r'.wacc, r'.fgroups, r'.xmem, r'.wmem, r'.ok);
            if valid_state_opaque(s0) {
                reveal_valid_state_opaque();
                code_state_validity(c0, s0, r1);
            }
            assert eval_code_lax(c0, s0, r1);
        } else {
            // If s0 isn't okay, we can do whatever we want,
            // so we ensure r1.ok is false, and hence eval_code_lax(*, r1, *) is trivially true
            r1 := s0;
        }
    }

    predicate {:opaque} eval_while_opaque(w:whileCond, c:code, n:nat, s:state, r:state)
    {
        eval_while(c, n, s, r)
    }

    predicate eval_while_lax(w:whileCond, c:code, n:nat, s:state, r:state)
    {
        s.ok ==> eval_while_opaque(w, c, n, s, r)
    }

    predicate va_whileInv(w:whileCond, c:code, n:int, r1: va_state, r2: va_state)
    {
        n >= 0 && valid_state_opaque(r1) && eval_while_lax(w, c, n, r1, r2)
    }

    lemma va_lemma_while(w:whileCond, c:code, s: va_state, r: va_state) returns(n:nat, r': va_state)
        // requires va_is_src_reg32(w.r, s);
        // requires va_is_src_imm32(w.c, s);
        requires valid_state_opaque(s);
        requires eval_code_lax(While(w, c), s, r)
        ensures  eval_while_lax(w, c, n, r', r)
        //ensures  r'.ok
        ensures s.ok ==> (n == eval_cond(s, w));
        ensures  valid_state_opaque(r');
        ensures r' == s
    {
        reveal_eval_code_opaque();
        reveal_valid_state_opaque();
        reveal_eval_while_opaque();
        if s.ok {
            assert eval_code(While(w, c), s, r);
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
        requires eval_while_lax(w, c, n, s, r)
        ensures  valid_state_opaque(s) ==> valid_state_opaque(s');
        ensures  eval_while_lax(w, c, n - 1, r', r)
        ensures  eval_code_lax(c, s', r');
        // ensures  valid_state_opaque(s) ==> if s.ok then BN_branchRelation(s, s', true) else s' == s;
        ensures  if s.ok && valid_state_opaque(s) then
                    && s'.ok
                    && s == s'
                    // && eval_cond(s, w) > 0
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
        assert eval_while(c, n, s, r); // TODO: Dafny reveal/opaque issue

        if valid_state_opaque(s) {
            var r'':state :| eval_code(c, s, r'') && eval_while( c, n - 1, r'', r);
            s' := s;
            r' := r'';
            code_state_validity(c, s', r'');
        } else {
            s' := s.(ok := false);
            r' := s.(ok := false);
        }
    }

    lemma va_lemma_whileFalse(w:whileCond, c:code, s: va_state, r: va_state) returns(r': va_state)
        requires eval_while_lax(w, c, 0, s, r)
        ensures  if s.ok then
                    (if valid_state_opaque(s) then
                        (r'.ok ==> valid_state_opaque(r'))
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
        reveal_eval_code_opaque();
        reveal_eval_while_opaque();
        reveal_valid_state_opaque();

        if !s.ok {
            r' := s;
            return;
        }
        r' := r;
    }
}
