// Note that bv[0] is the LSB
type bv = seq<bool>

function bitwise_neg(a:bv) : (b:bv)
    ensures |b| == |a|
{
    if |a| == 0 then []
    else [!a[0]] + bitwise_neg(a[1..])
}

function bitwise_and(a:bv, b:bv) : (c:bv)
    requires |a| == |b|
    ensures  |c| == |a|
{
    if |a| == 0 then []
    else [a[0] && b[0]] + bitwise_and(a[1..], b[1..])    
}

function bitwise_or(a:bv, b:bv) : (c:bv)
    requires |a| == |b|
    ensures  |c| == |a|
{
    if |a| == 0 then []
    else [a[0] || b[0]] + bitwise_or(a[1..], b[1..])    
}

function xor(a:bool, b:bool) : bool
{
    (a || b) && (!a || !b)
}

function bitwise_add_carry(a:bv, b:bv, c:bool) : (sum:bv)
    requires |a| == |b|
    ensures  |sum| == |a|
{
    if |a| == 0 then []
    else 
        var sum := xor(xor(a[0], b[0]), c);
        var c' := (a[0] && b[0]) || (c && (a[0] || b[0]));
        [sum] + bitwise_add_carry(a[1..], b[1..], c')
}

function bitwise_add(a:bv, b:bv) : bv
    requires |a| == |b|
{
    bitwise_add_carry(a, b, false) 
}

datatype BinaryOp = And | Or | Add

datatype BVExpr =
    | Const(bv)
    | Var(string)
    | Neg(e:BVExpr)
    | BinaryOp(op:BinaryOp, lhs:BVExpr, rhs:BVExpr)
    
datatype CmpOp = Eq | Neq //| Lt 

datatype CmpExpr = CmpExpr(op:CmpOp, lhs:BVExpr, rhs:BVExpr)

datatype LogicalBinaryOp = And | Or

datatype LogicalExpr =
    | Cmp(e:CmpExpr)
    | Not(ex:LogicalExpr)
    | BinaryOp(op: LogicalBinaryOp, lhs:LogicalExpr, rhs:LogicalExpr)

type store = map<string, bv>
predicate ConsistentStore(s:store, w:nat) 
{
    forall v :: v in s ==> |s[v]| == w
}

datatype Option<V> = None | Some(v:V)
function EvalBV(s:store, e:BVExpr, width:nat) : (r:Option<bv>)
    requires ConsistentStore(s, width)
    ensures  r.Some? ==> |r.v| == width
{
    match e
        case Const(b) => if |b| >= width then Some(b[..width]) else None
        case Var(st) => if st in s then Some(s[st]) else None
        case Neg(e) => 
            (match EvalBV(s, e, width)
            case None => None
            case Some(b) => Some(bitwise_neg(b)))
        case BinaryOp(op, lhs, rhs) => 
            var lhs := EvalBV(s, lhs, width);
            var rhs := EvalBV(s, rhs, width);
            if lhs.None? || rhs.None? then None
            else
                match op
                case And => Some(bitwise_and(lhs.v, rhs.v))
                case Or  => Some(bitwise_or (lhs.v, rhs.v))
                case Add => Some(bitwise_add(lhs.v, rhs.v))
}

function EvalCmp(s:store, e:CmpExpr, width:nat) : Option<bool>
    requires ConsistentStore(s, width)
{
    var lhs := EvalBV(s, e.lhs, width);
    var rhs := EvalBV(s, e.rhs, width);
    if lhs.None? || rhs.None? then None
    else
        (match e.op
            case Eq => Some(lhs.v == rhs.v)
            case Neq => Some(lhs.v != rhs.v))
}

predicate ValidCmpExprWidth(e:CmpExpr, w:nat)
{
    forall s :: 
        ConsistentStore(s, w) &&
        EvalCmp(s, e, w).Some?
        ==>
        EvalCmp(s, e, w).v
}

predicate ValidCmpExpr(e:CmpExpr)
{
    forall s, width :: 
        ConsistentStore(s, width) &&
        EvalCmp(s, e, width).Some?
        ==>
        EvalCmp(s, e, width).v
}

function EvalLogicalExpr(s:store, e:LogicalExpr, width:nat) : Option<bool>
    requires ConsistentStore(s, width)
{
    match e
        case Cmp(e) => EvalCmp(s, e, width)        
        case Not(e) => 
            (match EvalLogicalExpr(s, e, width)
                case None => None
                case Some(b) => Some(!b))
        case BinaryOp(op, lhs, rhs) =>
            var lhs := EvalLogicalExpr(s, lhs, width);
            var rhs := EvalLogicalExpr(s, rhs, width);
            if lhs.None? || rhs.None? then None
            else 
                match op
                    case And => Some(lhs.v && rhs.v)
                    case Or  => Some(lhs.v || rhs.v)
}

predicate ValidLogicalExpr(e:LogicalExpr)
{
    forall s, width :: 
        ConsistentStore(s, width) &&
        EvalLogicalExpr(s, e, width).Some?
        ==>
        EvalLogicalExpr(s, e, width).v
}

function EvalBVTruncated(s:store, e:BVExpr, width:nat, t:nat) : (r:Option<bv>)
    requires ConsistentStore(s, width)
    requires t <= width
    ensures  r.Some? ==> |r.v| == t
{
    match e
        case Const(b) => if |b| >= t then Some(b[..t]) else None
        case Var(st) => if st in s then Some(s[st][..t]) else None
        case Neg(e) => 
            (match EvalBVTruncated(s, e, width, t)
            case None => None
            case Some(b) => Some(bitwise_neg(b)))
        case BinaryOp(op, lhs, rhs) => 
            var lhs := EvalBVTruncated(s, lhs, width, t);
            var rhs := EvalBVTruncated(s, rhs, width, t);
            if lhs.None? || rhs.None? then None
            else
                match op
                case And => Some(bitwise_and(lhs.v, rhs.v))
                case Or  => Some(bitwise_or (lhs.v, rhs.v))
                case Add => Some(bitwise_add(lhs.v, rhs.v))
}

lemma bitwise_neg_truncated(a:bv, t:nat)
    requires t <= |a|
    ensures bitwise_neg(a)[..t] == bitwise_neg(a[..t])
{
    if |a| == 0 {         
    } else {
        if t > 0 {
            calc {
                bitwise_neg(a)[..t];
                ([!a[0]] + bitwise_neg(a[1..]))[..t];
                 [!a[0]] + bitwise_neg(a[1..])[..t-1];
                    { bitwise_neg_truncated(a[1..], t-1); }
                 [!a[0]] + bitwise_neg(a[1..][..t-1]);
                    { assert a[1..][..t-1] == a[1..t]; }
                bitwise_neg(a[..t]);
            }
        }
    }
}

lemma bitwise_and_truncated(a:bv, b:bv, t:nat)
    requires t <= |a| == |b|
    ensures bitwise_and(a, b)[..t] == bitwise_and(a[..t], b[..t])
{
    if |a| == 0 {         
    } else {
        if t > 0 {
            calc {
                bitwise_and(a, b)[..t];
                ([a[0] && b[0]] + bitwise_and(a[1..], b[1..]))[..t];
                 [a[0] && b[0]] + bitwise_and(a[1..], b[1..])[..t-1];
                    { bitwise_and_truncated(a[1..], b[1..], t-1); }
                 [a[0] && b[0]] + bitwise_and(a[1..][..t-1], b[1..][..t-1]);
                    { assert a[1..][..t-1] == a[1..t];
                      assert b[1..][..t-1] == b[1..t];
                    }
                bitwise_and(a[..t], b[..t]);
            }
        }
    }
}

// TODO: Refactor definition of bitwise_* ops, so we can write this proof once
lemma bitwise_or_truncated(a:bv, b:bv, t:nat)
    requires t <= |a| == |b|
    ensures bitwise_or(a, b)[..t] == bitwise_or(a[..t], b[..t])
{
    if |a| == 0 {         
    } else {
        if t > 0 {
            calc {
                bitwise_or(a, b)[..t];
                ([a[0] || b[0]] + bitwise_or(a[1..], b[1..]))[..t];
                 [a[0] || b[0]] + bitwise_or(a[1..], b[1..])[..t-1];
                    { bitwise_or_truncated(a[1..], b[1..], t-1); }
                 [a[0] || b[0]] + bitwise_or(a[1..][..t-1], b[1..][..t-1]);
                    { assert a[1..][..t-1] == a[1..t];
                      assert b[1..][..t-1] == b[1..t];
                    }
                bitwise_or(a[..t], b[..t]);
            }
        }
    }
}

lemma bitwise_add_carry_truncated(a:bv, b:bv, c:bool, t:nat)
    requires t <= |a| == |b|
    ensures bitwise_add_carry(a, b, c)[..t] == bitwise_add_carry(a[..t], b[..t], c)
{
    if |a| == 0 {         
    } else {
        if t > 0 {
            var sum := xor(xor(a[0], b[0]), c);
            var c' := (a[0] && b[0]) || (c && (a[0] || b[0]));
            calc {
                bitwise_add_carry(a, b, c)[..t];
                ([sum] + bitwise_add_carry(a[1..], b[1..], c'))[..t];
                 [sum] + bitwise_add_carry(a[1..], b[1..], c')[..t-1];
                    { bitwise_add_carry_truncated(a[1..], b[1..], c', t-1); }
                 [sum] + bitwise_add_carry(a[1..][..t-1], b[1..][..t-1], c');
                    { assert a[1..][..t-1] == a[1..t];
                      assert b[1..][..t-1] == b[1..t];
                    }
                bitwise_add_carry(a[..t], b[..t], c);
            }
        }
    }
}

lemma EvalBVTruncated_same_store(s_w:store, e:BVExpr, width:nat, t:nat)
    requires t <= width
    requires ConsistentStore(s_w, width)
    requires EvalBV(s_w, e, width).Some?
    ensures  EvalBVTruncated(s_w, e, width, t).Some?
    ensures  EvalBVTruncated(s_w, e, width, t).v == EvalBV(s_w, e, width).v[..t]

{
    match e {
        case Const(b) => 
        case Var(st) => 
        case Neg(e) => 
            //EvalBVTruncated_same_store(s_w, e, width, t);
            var r_w := EvalBV(s_w, e, width).v;
            var r_t := EvalBVTruncated(s_w, e, width, t).v;
            bitwise_neg_truncated(r_w, t);
            assert bitwise_neg(r_t) == bitwise_neg(r_w)[..t];
        case BinaryOp(op, lhs, rhs) => 
            var l_w := EvalBV(s_w, lhs, width).v;
            var l_t := EvalBVTruncated(s_w, lhs, width, t).v;
            var r_w := EvalBV(s_w, rhs, width).v;
            var r_t := EvalBVTruncated(s_w, rhs, width, t).v;
            bitwise_and_truncated(l_w, r_w, t);
            bitwise_or_truncated(l_w, r_w, t);
            bitwise_add_carry_truncated(l_w, r_w, false, t);
    }
}


lemma EvalBVTruncated_properties(s_w:store, s_t:store, e:BVExpr, width:nat, t:nat)
    requires t <= width
    requires ConsistentStore(s_w, width)
    requires ConsistentStore(s_t, t)
    requires s_w.Keys == s_t.Keys
    requires forall k :: k in s_w.Keys ==> s_w[k][..t] == s_t[k]
    requires EvalBV(s_w, e, width).Some?
    ensures  EvalBV(s_t, e, t).Some?
    ensures  EvalBVTruncated(s_w, e, width, t).Some?
    ensures  EvalBV(s_t, e, t).v == EvalBVTruncated(s_w, e, width, t).v == EvalBV(s_w, e, width).v[..t]
{
    EvalBVTruncated_same_store(s_w, e, width, t);
    match e {
        case Const(b) => 
        case Var(st) =>
        case Neg(e) => 
            EvalBVTruncated_properties(s_w, s_t, e, width, t);
        case BinaryOp(op, lhs, rhs) =>  
            EvalBVTruncated_properties(s_w, s_t, lhs, width, t);
            EvalBVTruncated_properties(s_w, s_t, rhs, width, t);
    }
}

function TruncateStore(s:store, w:nat, t:nat) : (s':store)
    requires ConsistentStore(s, w)
    requires t <= w
    ensures  ConsistentStore(s',t)
{
    map k | k in s :: s[k][..t]
}

lemma ValidityImplication(e:CmpExpr, m:nat, n:nat)
    requires e.op.Neq?
    requires n > m
    requires ValidCmpExprWidth(e, m)
    ensures  ValidCmpExprWidth(e, n)
{
    if !ValidCmpExprWidth(e, n) {
        assert exists s :: !(ConsistentStore(s, n) && EvalCmp(s, e, n).Some? ==> EvalCmp(s, e, n).v);
        var s :| !(ConsistentStore(s, n) && EvalCmp(s, e, n).Some? ==> EvalCmp(s, e, n).v);

        if !ConsistentStore(s, n) || !EvalCmp(s, e, n).Some? {
            assert !ValidCmpExprWidth(e, m);
        } else {
            assert EvalCmp(s, e, n).Some?;
            assert !EvalCmp(s, e, n).v;
            var l := EvalBV(s, e.lhs, n).v;
            var r := EvalBV(s, e.rhs, n).v;
            assert l == r;
            var s' := TruncateStore(s, n, m);
            EvalBVTruncated_properties(s, s', e.lhs, n, m);
            EvalBVTruncated_properties(s, s', e.rhs, n, m);
            assert EvalBV(s', e.lhs, m).v == l[..m];
            assert EvalBV(s', e.rhs, m).v == r[..m];
            assert !EvalCmp(s', e, m).v;
            assert !ValidCmpExprWidth(e, m);
        }
        assert !ValidCmpExprWidth(e, m);  // Proof by contradiction
    }
}