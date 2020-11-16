#![allow(dead_code)]

use egg::{rewrite as rw, *};
use std::collections::HashMap;
use std::fmt;

enum BVBinOp {
    And,
    Or,
    Xor,
    Add,
    Sub,
}
enum BVUniOp {
    Neg,
}

enum BVexpr {
    Const(i64),
    Var(String),
    UniExpr(BVUniOp, Box<BVexpr>),
    BinExpr(BVBinOp, Box<BVexpr>, Box<BVexpr>),
}

impl fmt::Display for BVexpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use BVexpr::*;
        match &*self {
            Const(c) => write!(f, "{}", c),
            Var(v) => write!(f, "{}", v),
            UniExpr(_op, boxed_src) => write!(f, "~{}", boxed_src),
            BinExpr(op, boxed_src0, boxed_src1) => {
                use BVBinOp::*;
                let op_str = match op {
                    And => "&",
                    Or => "|",
                    Xor => "^",
                    Add => "+",
                    Sub => "-",
                };
                write!(f, "({} {} {})", boxed_src0, op_str, boxed_src1)
            }
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
enum BoolBinOp {
    And,
    Or,
    Xor,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
enum BoolUniOp {
    Not,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
enum Boolexpr {
    Const(i64),
    Var(String),
    UniExpr(BoolUniOp, Box<Boolexpr>),
    BinExpr(BoolBinOp, Box<Boolexpr>, Box<Boolexpr>),
}

impl fmt::Display for Boolexpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &*self {
            Boolexpr::Const(c) => write!(f, "{}", c),
            Boolexpr::Var(v) => write!(f, "{}", v),
            Boolexpr::UniExpr(_op, boxed_src) => write!(f, "~{}", boxed_src),
            Boolexpr::BinExpr(op, boxed_src0, boxed_src1) => {
                let op_str = match op {
                    BoolBinOp::And => "&",
                    BoolBinOp::Or => "|",
                    BoolBinOp::Xor => "^",
                };
                write!(f, "({} {} {})", boxed_src0, op_str, boxed_src1)
            }
        }
    }
}

struct Namer {
    ctr:u32,
}

impl Namer {
    pub fn new() -> Namer {
        Namer { ctr : 0 }
    }

    fn get_name(& mut self, s:&str) -> String {
        self.ctr = self.ctr + 1;
        format!("{}_{}", s, self.ctr)
    }
}


fn get_bit_exprs(e: BVexpr, n:& mut Namer) -> (Boolexpr, Option<HashMap<Boolexpr, Boolexpr>>) {
    match e {
        BVexpr::Const(c) => (Boolexpr::Const(c), None),
        BVexpr::Var(v) => (Boolexpr::Var(v), None),
        BVexpr::UniExpr(_op, boxed_src) => {
            let (src, map) = get_bit_exprs(*boxed_src, n);
            (Boolexpr::UniExpr(BoolUniOp::Not, Box::new(src)), map)
        }
        BVexpr::BinExpr(op, boxed_src0, boxed_src1) => {
            let (src0, map0) = get_bit_exprs(*boxed_src0, n);
            let (src1, map1) = get_bit_exprs(*boxed_src1, n);
            let maps = match map0 {
                None => map1,
                Some(m0) => match map1 {
                    None => None,
                    Some(m1) => {
                        let mut fresh_map = HashMap::new();
                        fresh_map.extend(m0.into_iter());
                        fresh_map.extend(m1.into_iter());
                        Some(fresh_map)
                    }
                },
            };
            let src0 = Box::new(src0);
            let src1 = Box::new(src1);
            match op {
                BVBinOp::And => (Boolexpr::BinExpr(BoolBinOp::And, src0, src1), maps),
                BVBinOp::Or => (Boolexpr::BinExpr(BoolBinOp::Or, src0, src1), maps),
                BVBinOp::Xor => (Boolexpr::BinExpr(BoolBinOp::Xor, src0, src1), maps),
                BVBinOp::Add => {
                    let carry_var = Box::new(Boolexpr::Var(n.get_name("carry"))); // TODO: Pick a unique name
                    let carry_expr = Boolexpr::BinExpr(
                        BoolBinOp::Or,
                        Box::new(Boolexpr::BinExpr(
                            BoolBinOp::And,
                            src0.clone(),
                            src1.clone(),
                        )),
                        Box::new(Boolexpr::BinExpr(
                            BoolBinOp::And,
                            carry_var.clone(),
                            Box::new(Boolexpr::BinExpr(BoolBinOp::Or, src0.clone(), src1.clone())),
                        )),
                    );
                    let maps = if let Some(mut m) = maps {
                        m.insert(*carry_var.clone(), carry_expr);
                        Some(m)
                    } else {
                        None
                    };
                    let add_expr = Boolexpr::BinExpr(
                        BoolBinOp::Xor,
                        src0,
                        Box::new(Boolexpr::BinExpr(BoolBinOp::Xor, src1, carry_var)),
                    );
                    (add_expr, maps)
                }
                BVBinOp::Sub => panic!("This should be gone by now!"),
            }
        }
    }
}

fn simp_bv(e: BVexpr) -> BVexpr {
    match e {
        BVexpr::Const(_) => e,
        BVexpr::Var(_) => e,
        BVexpr::UniExpr(op, boxed_src) => BVexpr::UniExpr(op, Box::new(simp_bv(*boxed_src))),
        BVexpr::BinExpr(op, boxed_src0, boxed_src1) => {
            let s0 = Box::new(simp_bv(*boxed_src0));
            let s1 = Box::new(simp_bv(*boxed_src1));
            match op {
                BVBinOp::Sub => BVexpr::BinExpr(
                    BVBinOp::Add,
                    s0,
                    Box::new(BVexpr::BinExpr(
                        BVBinOp::Add,
                        Box::new(BVexpr::UniExpr(BVUniOp::Neg, s1)),
                        Box::new(BVexpr::Const(1)),
                    )),
                ),
                _ => BVexpr::BinExpr(op, s0, s1),
            }
        }
    }
}

fn identity() -> BVexpr {
    let x1 = Box::new(BVexpr::Var("x".to_owned()));
    let x2 = Box::new(BVexpr::Var("x".to_owned()));
    BVexpr::BinExpr(BVBinOp::Sub, x1, x2)
}

fn simple_example() {
    let f = identity();
    println!("Original BV expr: {}", f);
    let f = simp_bv(f);
    println!("Simplified BV expr: {}", f);

    let mut namer = Namer::new();
    let (f_expr, carries) = get_bit_exprs(f, &mut namer);
    println!("Main bool expr: {}", f_expr);
    if let Some(m) = carries {
        for (carry, carry_expr) in m.into_iter() {
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
