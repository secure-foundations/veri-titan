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

function method xor(a:bool, b:bool) : bool
{
    (a || b) && (!a || !b)
}

function min(a:int, b:int) : int {
	  if a < b then a else b
}

function bitwise_lsh(a:bv, b:nat) : (c:bv)
	ensures |c| == |a|
{
    seq(min(b, |a|), n => false) + a[0..(|a| - min(|a|, b))]
}

function bitwise_rsh(a:bv, b:nat) : (c:bv)
	ensures |c| == |a|
{
    var num_0s := min(b, |a|);
    a[num_0s..] + seq(num_0s, n => false)
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

function method bitwise_mul_partial(a:bv, b:bv, i:nat, j:nat) : (part:bool)
	requires j <= i < |a| == |b|
	decreases i - j
{
	if j == i then a[j] && b[0]
	else
		xor(a[j] && b[i-j], bitwise_mul_partial(a, b, i, j+1))
}

function method bitwise_mul(a:bv, b:bv) : (prod:bv)
	requires |a| == |b|
	ensures |prod| == |a|
{
	if |a| == 0 then []
	else
		seq(|a|, (n:nat) => if n < |a| then bitwise_mul_partial(a, b, n, 0) else false)
}

// test for bitwise_mul
method Main()
{
	var a := [false, false]; // 0
	var b := [true, true]; // 3
	var c := [true, false]; // 1
	var d := [false, true]; // 2

  if bitwise_mul(a, b) == a { print "ok1\n"; }
  if bitwise_mul(a, c) == a { print "ok2\n"; }
  if bitwise_mul(a, d) == a { print "ok3\n"; }
  if bitwise_mul(b, c) == b { print "ok4\n"; }
  if bitwise_mul(b, d) == d { print "ok5\n"; } // (3 * 2) % 4 == 2
  if bitwise_mul(c, d) == d { print "ok6\n"; }
}

datatype BinaryOp = And | Or | Add | Mul
datatype ShiftOp = Lsh | Rsh

datatype BVExpr =
    | Const(bv)
    | Var(string)
    | Neg(e:BVExpr)
    | BinaryOp(op:BinaryOp, lhs:BVExpr, rhs:BVExpr)
	| ShiftOp(sh:ShiftOp, bve:BVExpr, amt:nat)

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
                (match op
                case And => Some(bitwise_and(lhs.v, rhs.v))
                case Or  => Some(bitwise_or (lhs.v, rhs.v))
                case Add => Some(bitwise_add(lhs.v, rhs.v))
				        case Mul => Some(bitwise_mul(lhs.v, rhs.v)))
				case ShiftOp(sh, bve, amt) =>
					var bve := EvalBV(s, bve, width);
					if bve.None? then None
					else
						match sh
						case Lsh => Some(bitwise_lsh(bve.v, amt))
                        case Rsh => Some(bitwise_rsh(bve.v, amt))

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
