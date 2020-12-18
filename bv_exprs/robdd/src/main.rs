#![allow(dead_code, unused_variables, unused_imports)]

use std::collections::HashSet;
use std::rc::Rc;

#[derive(Debug, Clone)]
enum Expr_ {
    Const(bool),
    Variable(String),
    Not(Expr),
    And(Expr, Expr),
    Or(Expr, Expr),
    Xor(Expr, Expr),
}
type Expr = Rc<Expr_>;

impl std::fmt::Display for Expr_ {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use Expr_::*;
        match self {
            Const(b) => write!(f, "{}", b),
            Variable(v) => write!(f, "{}", v),
            Not(e) => write!(f, "(~ {})", e),
            And(a, b) => write!(f, "(& {} {})", a, b),
            Or(a, b) => write!(f, "(| {} {})", a, b),
            Xor(a, b) => write!(f, "(^ {} {})", a, b),
        }
    }
}

#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
enum BDD_ {
    Sink {
        value: bool,
    },
    Node {
        var: String,
        if_true: BDD,
        if_false: BDD,
    },
}
type BDD = Rc<BDD_>;

/// Gets the value within `s` if it exists; if not, it inserts it and
/// then gets it.
fn as_member<T, X>(s: &mut HashSet<Rc<T>>, v: X) -> Rc<T>
where
    T: Eq + std::hash::Hash,
    X: Into<Rc<T>>,
{
    let v = v.into();
    match s.get(&v) {
        None => {
            s.insert(v.clone());
            v
        }
        Some(x) => x.clone(),
    }
}

impl Expr_ {
    fn to_robdd(&self, var_ordering: &[&str]) -> BDD {
        use Expr_::*;
        use BDD_::*;

        fn f(e: &Expr_, var_ordering: &[&str], bdd_nodes: &mut HashSet<BDD>) -> BDD {
            match e {
                Const(b) => as_member(bdd_nodes, Sink { value: *b }),
                Variable(x) => {
                    let tt = f(&Const(true), var_ordering, bdd_nodes);
                    let ff = f(&Const(false), var_ordering, bdd_nodes);
                    as_member(
                        bdd_nodes,
                        Node {
                            var: x.into(),
                            if_true: tt,
                            if_false: ff,
                        },
                    )
                }
                Not(e) => f(e, var_ordering, bdd_nodes).negate_using(bdd_nodes),
                And(a, b) => {
                    let a = f(a, var_ordering, bdd_nodes);
                    let b = f(b, var_ordering, bdd_nodes);
                    a.apply_binop_using(|x, y| x && y, &b, var_ordering, bdd_nodes)
                }
                Or(a, b) => {
                    let a = f(a, var_ordering, bdd_nodes);
                    let b = f(b, var_ordering, bdd_nodes);
                    a.apply_binop_using(|x, y| x || y, &b, var_ordering, bdd_nodes)
                }
                Xor(a, b) => {
                    let a = f(a, var_ordering, bdd_nodes);
                    let b = f(b, var_ordering, bdd_nodes);
                    a.apply_binop_using(|x, y| x ^ y, &b, var_ordering, bdd_nodes)
                }
            }
        }

        f(self, var_ordering, &mut HashSet::new())
    }
}

impl BDD_ {
    fn negate_using(&self, bdd_nodes: &mut HashSet<BDD>) -> BDD {
        use BDD_::*;

        match self {
            Sink { value: b } => as_member(bdd_nodes, Sink { value: !b }),
            Node {
                var,
                if_true,
                if_false,
            } => {
                let if_true = if_true.negate_using(bdd_nodes);
                let if_false = if_false.negate_using(bdd_nodes);
                as_member(
                    bdd_nodes,
                    Node {
                        var: var.into(),
                        if_true,
                        if_false,
                    },
                )
            }
        }
    }

    fn reduce_once_using(self, bdd_nodes: &mut HashSet<BDD>) -> BDD {
        use BDD_::*;
        match self {
            Sink { .. } => as_member(bdd_nodes, self),
            Node {
                var,
                if_true,
                if_false,
            } => {
                if Rc::ptr_eq(&if_true, &if_false) {
                    as_member(bdd_nodes, if_true)
                } else {
                    debug_assert!(
                        if_true != if_false,
                        "Pointer equality should imply actual equality in an ROBDD. \
                         This failed somehow."
                    );
                    as_member(
                        bdd_nodes,
                        Node {
                            var,
                            if_true,
                            if_false,
                        },
                    )
                }
            }
        }
    }

    fn apply_binop_using<F>(
        &self,
        binop: F,
        other: &Self,
        var_ordering: &[&str],
        bdd_nodes: &mut HashSet<BDD>,
    ) -> BDD
    where
        F: Fn(bool, bool) -> bool + Copy,
    {
        use BDD_::*;
        match (self, other) {
            (Sink { value: v1 }, Sink { value: v2 }) => as_member(
                bdd_nodes,
                Sink {
                    value: binop(*v1, *v2),
                },
            ),
            (
                Node {
                    var: v1,
                    if_true: t1,
                    if_false: f1,
                },
                Sink { value: v2 },
            ) => {
                let tt = t1.apply_binop_using(binop, other, var_ordering, bdd_nodes);
                let ff = f1.apply_binop_using(binop, other, var_ordering, bdd_nodes);
                Node {
                    var: v1.into(),
                    if_true: tt,
                    if_false: ff,
                }
                .reduce_once_using(bdd_nodes)
            }
            (
                Sink { value: v1 },
                Node {
                    var: v2,
                    if_true: t2,
                    if_false: f2,
                },
            ) => {
                let tt = self.apply_binop_using(binop, t2, var_ordering, bdd_nodes);
                let ff = self.apply_binop_using(binop, f2, var_ordering, bdd_nodes);
                Node {
                    var: v2.into(),
                    if_true: tt,
                    if_false: ff,
                }
                .reduce_once_using(bdd_nodes)
            }
            (
                Node {
                    var: v1,
                    if_true: t1,
                    if_false: f1,
                },
                Node {
                    var: v2,
                    if_true: t2,
                    if_false: f2,
                },
            ) => {
                assert_ne!(var_ordering.len(), 0);
                match (v1 == var_ordering[0], v2 == var_ordering[0]) {
                    (false, false) => {
                        self.apply_binop_using(binop, other, &var_ordering[1..], bdd_nodes)
                    }
                    (true, false) => {
                        let tt = t1.apply_binop_using(binop, other, var_ordering, bdd_nodes);
                        let ff = f1.apply_binop_using(binop, other, var_ordering, bdd_nodes);
                        Node {
                            var: v1.into(),
                            if_true: tt,
                            if_false: ff,
                        }
                        .reduce_once_using(bdd_nodes)
                    }
                    (false, true) => {
                        let tt = self.apply_binop_using(binop, t2, var_ordering, bdd_nodes);
                        let ff = self.apply_binop_using(binop, f2, var_ordering, bdd_nodes);
                        Node {
                            var: v2.into(),
                            if_true: tt,
                            if_false: ff,
                        }
                        .reduce_once_using(bdd_nodes)
                    }
                    (true, true) => {
                        let tt = t1.apply_binop_using(binop, t2, var_ordering, bdd_nodes);
                        let ff = f1.apply_binop_using(binop, f2, var_ordering, bdd_nodes);
                        Node {
                            var: v1.into(),
                            if_true: tt,
                            if_false: ff,
                        }
                        .reduce_once_using(bdd_nodes)
                    }
                }
            }
        }
    }
}

impl Expr_ {
    /// Basic handwritten parser for `Expr` with some amount of error
    /// handling.
    fn from_str(s: &str) -> Result<Expr, String> {
        fn parse(s: &str) -> Result<(Expr, &str), String> {
            let s = s.trim();
            match s.chars().nth(0) {
                None => Err("End of string".into()),
                Some('(') => {
                    let s = &s[1..].trim();
                    let (e, s) = parse(s)?;
                    let s = s.trim();
                    match s.chars().nth(0) {
                        None => Err("End of string. Expected `)`.".into()),
                        Some(')') => Ok((e, &s[1..])),
                        Some(x) => {
                            return Err(format!(
                                "Unexpected `{}` found in `{}`. Expected `)`.",
                                x, s
                            ))
                        }
                    }
                }
                Some('~') => {
                    let s = &s[1..];
                    let (e, s) = parse(s)?;
                    Ok((Expr_::Not(e).into(), s))
                }
                Some('&') => {
                    let s = &s[1..];
                    let (a, s) = parse(s)?;
                    let (b, s) = parse(s)?;
                    Ok((Expr_::And(a, b).into(), s))
                }
                Some('|') => {
                    let s = &s[1..];
                    let (a, s) = parse(s)?;
                    let (b, s) = parse(s)?;
                    Ok((Expr_::Or(a, b).into(), s))
                }
                Some('^') => {
                    let s = &s[1..];
                    let (a, s) = parse(s)?;
                    let (b, s) = parse(s)?;
                    Ok((Expr_::Xor(a, b).into(), s))
                }
                Some('1') => Ok((Expr_::Const(true).into(), &s[1..])),
                Some('0') => Ok((Expr_::Const(false).into(), &s[1..])),
                Some(x) => {
                    let v: String = s
                        .chars()
                        .take_while(|&c| c.is_alphanumeric() || c == '_')
                        .collect();
                    let s = &s[v.len()..];
                    if v.len() == 0 {
                        Err(format!("Unexpected `{}` found in `{}`.", x, s))
                    } else if v == "true" {
                        Ok((Expr_::Const(true).into(), s))
                    } else if v == "false" {
                        Ok((Expr_::Const(false).into(), s))
                    } else {
                        Ok((Expr_::Variable(v).into(), s))
                    }
                }
            }
        }

        Ok(parse(s)?.0)
    }
}

impl BDD_ {
    fn to_expr(&self) -> Expr {
        use Expr_::*;
        use BDD_::*;
        match self {
            Sink { value } => Const(*value).into(),
            Node {
                var,
                if_true,
                if_false,
            } => Or(
                And(Variable(var.into()).into(), if_true.to_expr()).into(),
                And(Not(Variable(var.into()).into()).into(), if_false.to_expr()).into(),
            )
            .into(),
        }
    }
}

impl Expr_ {
    fn peephole_optimize(&self) -> Expr {
        use Expr_::*;

        match self {
            Const(_) | Variable(_) => self.clone().into(),
            Not(x) => match &**x {
                Const(b) => Const(!b).into(),
                Variable(_) => self.clone().into(),
                Not(y) => y.clone(),
                And(a, b) => Or(
                    Not(a.clone()).peephole_optimize(),
                    Not(b.clone()).peephole_optimize(),
                )
                .peephole_optimize(),
                Or(a, b) => And(
                    Not(a.clone()).peephole_optimize(),
                    Not(b.clone()).peephole_optimize(),
                )
                .peephole_optimize(),
                Xor(a, b) => Xor(a.clone(), Not(b.clone()).peephole_optimize()).peephole_optimize(),
            },
            And(a, b) => {
                let a = a.peephole_optimize();
                let b = b.peephole_optimize();
                match (&*a, &*b) {
                    (Const(false), _) | (_, Const(false)) => Const(false).into(),
                    (Const(true), x) | (x, Const(true)) => x.clone().into(),
                    _ => And(a, b).into(),
                }
            }
            Or(a, b) => {
                let a = a.peephole_optimize();
                let b = b.peephole_optimize();
                match (&*a, &*b) {
                    (Const(true), _) | (_, Const(true)) => Const(true).into(),
                    (Const(false), x) | (x, Const(false)) => x.clone().into(),
                    _ => And(a, b).into(),
                }
            }
            Xor(a, b) => {
                let a = a.peephole_optimize();
                let b = b.peephole_optimize();
                match (&*a, &*b) {
                    (Const(true), x) | (x, Const(true)) => {
                        Not(x.clone().into()).peephole_optimize()
                    }
                    (Const(false), x) | (x, Const(false)) => x.clone().into(),
                    _ => Xor(a, b).into(),
                }
            }
        }
    }
}

impl BDD_ {
    fn variables(&self) -> HashSet<&str> {
        use BDD_::*;
        match self {
            Sink { .. } => HashSet::new(),
            Node {
                var,
                if_true,
                if_false,
            } => std::iter::once(var.as_str())
                .chain(if_true.variables().into_iter())
                .chain(if_false.variables().into_iter())
                .collect(),
        }
    }
}

impl Expr_ {
    fn variables(&self) -> HashSet<&str> {
        use Expr_::*;
        match self {
            Const(b) => HashSet::new(),
            Variable(v) => std::iter::once(v.as_str()).collect(),
            Not(e) => e.variables(),
            And(a, b) | Or(a, b) | Xor(a, b) => a
                .variables()
                .into_iter()
                .chain(b.variables().into_iter())
                .collect(),
        }
    }

    fn unused_variables(&self) -> HashSet<String> {
        let vars: Vec<_> = self.variables().into_iter().collect();
        let bdd = self.to_robdd(&vars);
        let bdd_vars = bdd.variables();
        self.variables()
            .difference(&bdd_vars)
            .map(|x| x.to_string())
            .collect()
    }

    fn remove_unused_variables(&self) -> Expr {
        fn replace_all(e: &Expr_, removed: &HashSet<String>, replacement: bool) -> Expr {
            use Expr_::*;
            match e {
                Const(b) => e.clone().into(),
                Variable(v) => {
                    if removed.contains(v) {
                        Const(replacement).into()
                    } else {
                        e.clone().into()
                    }
                }
                Not(e) => Not(replace_all(e, removed, replacement)).into(),
                And(a, b) => And(
                    replace_all(a, removed, replacement),
                    replace_all(b, removed, replacement),
                )
                .into(),
                Or(a, b) => Or(
                    replace_all(a, removed, replacement),
                    replace_all(b, removed, replacement),
                )
                .into(),
                Xor(a, b) => Xor(
                    replace_all(a, removed, replacement),
                    replace_all(b, removed, replacement),
                )
                .into(),
            }
        }

        replace_all(self, &self.unused_variables(), false)
    }

    fn optimize(&self) -> Expr {
        self.remove_unused_variables().peephole_optimize()
    }
}

fn main() {
    loop {
        let mut line = String::new();
        match std::io::stdin().read_line(&mut line) {
            Ok(0) => break,
            Ok(_) => match Expr_::from_str(&line) {
                Ok(e) => {
                    println!("Expr:      {}", e);
                    println!("Optimized: {}", e.optimize());
                }
                Err(e) => println!("Error in parsing: {}", e),
            },
            Err(e) => println!("Error reading from stdin: {}", e),
        }
    }
}
