#![allow(dead_code)]

use egg::{rewrite as rw, *};
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, Copy)]
enum BVBinOp {
    And,
    Or,
    Xor,
    Add,
    Sub,
}

impl std::fmt::Display for BVBinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use BVBinOp::*;
        match self {
            And => write!(f, "&"),
            Or => write!(f, "|"),
            Xor => write!(f, "^"),
            Add => write!(f, "+"),
            Sub => write!(f, "-"),
        }
    }
}

#[derive(Clone, Copy)]
enum BVUniOp {
    Neg,
}

impl std::fmt::Display for BVUniOp {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use BVUniOp::*;
        match self {
            Neg => write!(f, "~"),
        }
    }
}

#[derive(Clone)]
enum BVExpr_ {
    Const(i64),
    Var(String),
    UniExpr(BVUniOp, BVExpr),
    BinExpr(BVBinOp, BVExpr, BVExpr),
}
type BVExpr = Rc<BVExpr_>;

impl std::fmt::Display for BVExpr_ {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use BVExpr_::*;
        match self {
            Const(c) => write!(f, "{}", c),
            Var(v) => write!(f, "{}", v),
            UniExpr(op, src) => write!(f, "{}{}", op, src),
            BinExpr(op, src0, src1) => write!(f, "({} {} {})", src0, op, src1),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
enum BoolBinOp {
    And,
    Or,
    Xor,
}

impl std::fmt::Display for BoolBinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use BoolBinOp::*;
        match self {
            And => write!(f, "&"),
            Or => write!(f, "|"),
            Xor => write!(f, "^"),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
enum BoolUniOp {
    Not,
}

impl std::fmt::Display for BoolUniOp {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use BoolUniOp::*;
        match self {
            Not => write!(f, "~"),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
enum BoolExpr_ {
    Const(i64),
    Var(String),
    UniExpr(BoolUniOp, BoolExpr),
    BinExpr(BoolBinOp, BoolExpr, BoolExpr),
}
type BoolExpr = Rc<BoolExpr_>;

impl std::fmt::Display for BoolExpr_ {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use BoolExpr_::*;
        match &*self {
            Const(c) => write!(f, "{}", c),
            Var(v) => write!(f, "{}", v),
            UniExpr(op, src) => write!(f, "{}{}", op, src),
            BinExpr(op, src0, src1) => write!(f, "{} {} {}", src0, op, src1),
        }
    }
}

impl BVExpr_ {
    fn get_bit_exprs(&self) -> (BoolExpr, Option<HashMap<BoolExpr, BoolExpr>>) {
        use BVExpr_::*;
        match self {
            Const(c) => (BoolExpr_::Const(*c).into(), None),
            Var(v) => (BoolExpr_::Var(v.clone()).into(), None),
            UniExpr(op, src) => {
                let BVUniOp::Neg = *op; // will be optimized away
                                        // (since it is an irrefutable
                                        // assignment), but a good way
                                        // to confirm that we are
                                        // indeed getting a "neg" here
                                        // (and at a later point, when
                                        // we add an extra BVUniOp,
                                        // the compiler will complain
                                        // here, thus immediately
                                        // pointing us to where we
                                        // need to refactor).
                let (src, map) = src.get_bit_exprs();
                (BoolExpr_::UniExpr(BoolUniOp::Not, src).into(), map)
            }
            BinExpr(op, src0, src1) => {
                let (src0, map0) = src0.get_bit_exprs();
                let (src1, map1) = src1.get_bit_exprs();
                let maps = match map0 {
                    None => map1,
                    Some(m0) => match map1 {
                        // JB: I left this `None` as is, but is this
                        // _really_ what you mean, or is this a bug
                        // and you meant to return `m0` here?
                        None => None,
                        Some(m1) => Some(m0.into_iter().chain(m1.into_iter()).collect()),
                    },
                };
                match op {
                    BVBinOp::And => (BoolExpr_::BinExpr(BoolBinOp::And, src0, src1).into(), maps),
                    BVBinOp::Or => (BoolExpr_::BinExpr(BoolBinOp::Or, src0, src1).into(), maps),
                    BVBinOp::Xor => (BoolExpr_::BinExpr(BoolBinOp::Xor, src0, src1).into(), maps),
                    BVBinOp::Add => {
                        let carry_var: BoolExpr = BoolExpr_::Var("carry".into()).into(); // TODO: Pick a unique name
                        let carry_expr = BoolExpr_::BinExpr(
                            BoolBinOp::Or,
                            BoolExpr_::BinExpr(BoolBinOp::And, src0.clone(), src1.clone()).into(),
                            BoolExpr_::BinExpr(
                                BoolBinOp::And,
                                carry_var.clone(),
                                BoolExpr_::BinExpr(BoolBinOp::Or, src0.clone(), src1.clone())
                                    .into(),
                            )
                            .into(),
                        )
                        .into();
                        let maps = maps.and_then(|mut m| {
                            m.insert(carry_var.clone(), carry_expr);
                            Some(m)
                        });
                        let add_expr = BoolExpr_::BinExpr(
                            BoolBinOp::Xor,
                            src0,
                            BoolExpr_::BinExpr(BoolBinOp::Xor, src1, carry_var).into(),
                        )
                        .into();
                        (add_expr, maps)
                    }
                    BVBinOp::Sub => unreachable!(),
                }
            }
        }
    }
}

impl BVExpr_ {
    fn simp(&self) -> BVExpr {
        use BVExpr_::*;
        match self {
            Const(_) | Var(_) => self.clone().into(),
            UniExpr(op, src) => BVExpr_::UniExpr(*op, src.simp()).into(),
            BinExpr(op, src0, src1) => {
                let src0 = src0.simp();
                let src1 = src1.simp();
                match op {
                    BVBinOp::Sub => BVExpr_::BinExpr(
                        BVBinOp::Add,
                        src0,
                        BVExpr_::BinExpr(
                            BVBinOp::Add,
                            BVExpr_::UniExpr(BVUniOp::Neg, src1).into(),
                            BVExpr_::Const(1).into(),
                        )
                        .into(),
                    )
                    .into(),
                    _ => BVExpr_::BinExpr(*op, src0, src1).into(),
                }
            }
        }
    }

    fn identity() -> Self {
        use BVBinOp::*;
        use BVExpr_::*;

        let x: BVExpr = Var("x".into()).into();
        BinExpr(Sub, x.clone(), x)
    }
}

fn simple_example() {
    let f = BVExpr_::identity();
    println!("Original BV expr: {}", f);
    let f = f.simp();
    println!("Simplified BV expr: {}", f);

    let (f_expr, carries) = f.get_bit_exprs();
    println!("Main bool expr: {}", f_expr);
    if let Some(m) = carries {
        for (carry, carry_expr) in m.iter() {
            println!("{} = {}", carry, carry_expr);
        }
    }
}

fn egg_test() {
    let rules: &[Rewrite<SymbolLang, ()>] = &[
        //    rw!("commute-and"; "(& ?x ?y)" => "(& ?y ?x)"),
        //    rw!("commute-or";  "(| ?x ?y)" => "(| ?y ?x)"),
        rw!("commute-xor"; "(^ ?x ?y)" => "(^ ?y ?x)"),
        //    rw!("xor";         "(^ ?x ?y)" => "(& (| ?x ?y) (| (~ x) (~ y)))"),

        //    rw!("dist-or-and"; "(| ?x (& ?y ?z))" => "(& (| ?x ?y) (| ?x ?z))"),
        //    rw!("dist-and-or"; "(& ?x (| ?y ?z))" => "(| (& ?x ?y) (& ?x ?z))"),
        //    rw!("dist-xor-or"; "(^ ?x (| ?y ?z))" => "(| (& (~ ?x) (| ?y ?z)) (& ?x (& (~ y) (~ z))))"),
        //    rw!("dist-and-xor"; "(& ?x (^ ?y ?z))"=> "(^ (& ?x ?y) (& ?x ?z))"),
        rw!("assoc-xor"; "(^ ?x (^ ?y ?z))"=> "(^ (^ ?x ?y) ?z)"),
        //
        //
        //    rw!("demorgan"; "(~ (^ ?x ?y))" => "(| (~ ?y) (~ ?x))"),
        //
        //    rw!("and-False"; "(& ?x False)" => "False"),
        //    rw!("and-True"; "(& ?x True)" => "?x"),
        //    rw!("and-self"; "(& ?x ?x)" => "?x"),
        //    rw!("and-self-neg"; "(& ?x (~ ?x))" => "False"),
        //
        //    rw!("or-False";  "(| ?x False)" => "?x"),
        //    rw!("or-True";  "(| ?x True)" => "True"),
        //    rw!("or-self";  "(| ?x ?x)" => "?x"),
        //    rw!("or-self-neg";  "(| ?x (~ ?x))" => "True"),
        rw!("xor-False"; "(^ ?x False)" => "?x"),
        rw!("xor-True"; "(^ ?x True)" => "(~ ?x)"),
        rw!("xor-self";   "(^ ?x ?x)" => "False"),
        rw!("xor-self-neg"; "(^ ?x (~ ?x))" => "True"),
        rw!("neg-dbl"; "(~ (~ ?x))" => "?x"),
    ];

    // While it may look like we are working with numbers,
    // SymbolLang stores everything as strings.
    // We can make our own Language later to work with other types.
    //let start = "(| True (& True True))".parse().unwrap();
    let start = "(^ x (^ (^ (~ x) (^ False carry_3)) carry_5))"
        .parse()
        .unwrap();

    // That's it! We can run equality saturation now.
    let runner = Runner::default().with_expr(&start).run(rules);

    // Extractors can take a user-defined cost function,
    // we'll use the egg-provided AstSize for now
    let mut extractor = Extractor::new(&runner.egraph, AstSize);

    // We want to extract the best expression represented in the
    // same e-class as our initial expression, not from the whole e-graph.
    // Luckily the runner stores the eclass Id where we put the initial expression.
    let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);

    // we found the best thing, which is just "a" in this case
    //    assert_eq!(best_expr, "a".parse().unwrap());
    //    assert_eq!(best_cost, 1);
    println!("Starting from: {}", start);
    println!("Best expr: {}", best_expr);
    println!("Cost: {}", best_cost);
}

fn main() {
    println!("Hello, world!");

    //egg_test();
    simple_example();

    println!("Done!");
}
