include "bv-semantics.dfy"

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
                (match op
                case And => Some(bitwise_and(lhs.v, rhs.v))
                case Or  => Some(bitwise_or (lhs.v, rhs.v))
                case Add => Some(bitwise_add(lhs.v, rhs.v))
                case Mul => Some(bitwise_mul(lhs.v, rhs.v)))
			  case ShiftOp(sh, bve, amt) =>
				    var bve := EvalBVTruncated(s, bve, width, t);
					  if bve.None? then None
						else
							(match sh
							case Lsh => Some(bitwise_lsh(bve.v, amt)))
}

// TODO: Refactor definition of bitwise_* ops, so we can write this proof once
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

lemma bitwise_lsh_truncated(a:bv, amt:nat, t:nat)
	  requires t <= |a|
    ensures bitwise_lsh(a, amt)[..t] == bitwise_lsh(a[..t], amt)
{
    if |a| == 0 {
    } else {
			    calc {
						bitwise_lsh(a, amt)[..t];
						(seq(min(amt, |a|), n => false) + a[0..(|a| - min(amt, |a|))])[..t];
						(seq(min(amt, |a[..t]|), n => false) + a[..t][0..(|a[..t]| - min(amt, |a[..t]|))]);
						bitwise_lsh(a[..t], amt);
				}
    }
}

lemma bitwise_mul_partial_truncated(a:bv, b:bv, i: nat, j:nat, t:nat)
	  requires j <= i < t <= |a| == |b|
    ensures (bitwise_mul_partial(a, b, i, j) == bitwise_mul_partial(a[..t], b[..t], i, j))
		decreases i - j
{
	if j == i {
	} else {
		calc {
			bitwise_mul_partial(a, b, i, j);
			xor(a[j] && b[i-j], bitwise_mul_partial(a, b, i, j+1));
			    { bitwise_mul_partial_truncated(a, b, i, j+1, t); }
			xor(a[..t][j] && b[..t][i-j], bitwise_mul_partial(a[..t], b[..t], i, j+1));
			bitwise_mul_partial(a[..t], b[..t], i, j);
		}
	}
}

lemma bitwise_mul_truncated(a:bv, b:bv, t:nat)
	  requires t <= |a| == |b|
    ensures bitwise_mul(a, b)[..t] == bitwise_mul(a[..t], b[..t])
{
	if |a| == 0 {
	} else {
		  calc {
				bitwise_mul(a, b)[..t];
			  (seq(|a|, (n:nat) => if n < |a| then bitwise_mul_partial(a, b, n, 0) else false)[..t]);
				    { forall n | 0 <= n < t ensures bitwise_mul_partial(a, b, n, 0) == bitwise_mul_partial(a[..t], b[..t], n, 0)
                { bitwise_mul_partial_truncated(a, b, n, 0, t); }
						}
			  (seq(|a[..t]|, (n:nat) => if n < |a[..t]| then bitwise_mul_partial(a[..t], b[..t], n, 0) else false));
				bitwise_mul(a[..t], b[..t]);
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
						bitwise_mul_truncated(l_w, r_w, t);
			  case ShiftOp(sh, bve, amt) =>
				    var l_w := EvalBV(s_w, bve, width).v;
					  var l_t := EvalBVTruncated(s_w, bve, width, t).v;
						bitwise_lsh_truncated(l_w, amt, t);
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
			case ShiftOp(sh, bve, amt) =>
				    EvalBVTruncated_properties(s_w, s_t, bve, width, t);
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
    requires m < n
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
