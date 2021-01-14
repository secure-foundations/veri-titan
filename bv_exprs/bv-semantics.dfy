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

