#![allow(dead_code)]

use egg::{*, rewrite as rw};
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
        use BVBinOp::*;
        match &*self {
            Const(c) => write!(f, "{}", c),
            Var(v) => write!(f, "{}", v),
            UniExpr(op, boxed_src) => { 
                let BVUniOp::Neg = *op;
                write!(f, "~{}", boxed_src)
            },
            BinExpr(op, boxed_src0, boxed_src1) => {
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
    Const(bool),
    Var(String,bool),
    UniExpr(BoolUniOp, Box<Boolexpr>),
    BinExpr(BoolBinOp, Box<Boolexpr>, Box<Boolexpr>),
}

impl Boolexpr {
    fn mk_string(&self, inline:bool, dafny:bool) -> String {
        use Boolexpr::*;
        match &*self {
            Const(c) => format!("{}", c),
            Var(v,old) => 
                if *old {
                    format!("old_{}", v)
                } else {
                    format!("{}", v)
                }
            UniExpr(op, boxed_src) => {
                let BoolUniOp::Not = *op;
                let src = (*boxed_src).mk_string(inline, dafny);
                if inline {
                    format!("(~ {})", src)
                } else if dafny {
                    format!("!{}", src)
                } else {
                    format!("~{}", src)
                }
            },
            BinExpr(op, boxed_src0, boxed_src1) => {
                use BoolBinOp::*;
                let s0 = boxed_src0.mk_string(inline, dafny);
                let s1 = boxed_src1.mk_string(inline, dafny);
                if dafny {
                    match op {
                        And => format!("({} && {})", s0, s1),
                        Or  => format!("({} || {})", s0, s1),
                        Xor => format!("xor({}, {})", s0, s1),
                    }
                } else {
                    let op_str = match op {
                        And => "&",
                        Or => "|",
                        Xor => "^",
                    };
                    if inline {
                        format!("({} {} {})", op_str, s0, s1)
                    } else {
                        format!("({} {} {})", s0, op_str, s1)
                    }
                }
            }
        }
    }
}

impl fmt::Display for Boolexpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.mk_string(false, true))
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
    use Boolexpr::*;
    use BoolBinOp::*;
    match e {
        BVexpr::Const(_c) => (Const(false), None),
        BVexpr::Var(v) => (Var(v, false), None),
        BVexpr::UniExpr(_op, boxed_src) => {
            let (src, map) = get_bit_exprs(*boxed_src, n);
            (UniExpr(BoolUniOp::Not, Box::new(src)), map)
        }
        BVexpr::BinExpr(op, boxed_src0, boxed_src1) => {
            let (src0, map0) = get_bit_exprs(*boxed_src0, n);
            let (src1, map1) = get_bit_exprs(*boxed_src1, n);
            let maps = match map0 {
                None => map1,
                Some(m0) => match map1 {
                    None => Some(m0),
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
                BVBinOp::And => (BinExpr(And, src0, src1), maps),
                BVBinOp::Or => (BinExpr(Or, src0, src1), maps),
                BVBinOp::Xor => (BinExpr(Xor, src0, src1), maps),
                BVBinOp::Add => {
                    let carry_name = n.get_name("carry");
                    let carry_var = Box::new(Var(carry_name.clone(), false));
                    let carry_expr = BinExpr(
                        Or,
                        Box::new(BinExpr(
                            And,
                            src0.clone(),
                            src1.clone(),
                        )),
                        Box::new(BinExpr(
                            And,
                            Box::new(Var(carry_name, true)),
                            Box::new(BinExpr(Or, src0.clone(), src1.clone())),
                        )),
                    );
                    let maps = if let Some(mut m) = maps {
                        m.insert(*carry_var.clone(), carry_expr);
                        Some(m)
                    } else {
                        let mut fresh_map = HashMap::new();
                        fresh_map.insert(*carry_var.clone(), carry_expr);
                        Some(fresh_map)
                    };
                    let add_expr = BinExpr(
                        Xor,
                        src0,
                        Box::new(BinExpr(Xor, src1, carry_var)),
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

fn subst_vars(e: Boolexpr, map:&HashMap<Boolexpr, Boolexpr>) -> Boolexpr {
    use Boolexpr::*;
    match &e {
        Const(_) => e,
        Var(_,old) => 
            if !old {
                match map.get(&e) {
                    None => e,
                    Some(rhs) => (*rhs).clone()
                }
            } else {
                e
            }
        UniExpr(op, boxed_src) => UniExpr(*op, Box::new(subst_vars((**boxed_src).clone(), map))),
        BinExpr(op, boxed_src0, boxed_src1) => {
            let s0 = subst_vars((**boxed_src0).clone(), map);
            let s1 = subst_vars((**boxed_src1).clone(), map);
            BinExpr(*op, Box::new(s0), Box::new(s1))
        }
    }
}

fn identity() -> BVexpr {
    use BVexpr::*;
    use BVBinOp::*;
    let x1 = Box::new(Var("x".to_owned()));
    let x2 = Box::new(Var("x".to_owned()));
    BinExpr(Sub, x1, x2)
}

fn simple_example() {
    let f = identity();
    println!("Original BV expr: {}", f);
    let f = simp_bv(f);
    println!("Simplified BV expr: {}", f);

    let mut namer = Namer::new();
    let (f_expr, carries) = get_bit_exprs(f, &mut namer);
    println!("Main bool expr: {}", f_expr);
    println!("Main bool expr inline: {}", f_expr.mk_string(true, false));
    
    let rules = egg_rules();
    let f_egg = egg_simp(f_expr.mk_string(true, false), &rules);
    println!("Main bool expr simplified: {}", f_egg);


    if let Some(m) = carries {
        for (carry, carry_expr) in &m {
            println!("{} = {}", carry, carry_expr);
            let carry_expr_egg = egg_simp(carry_expr.mk_string(true, false), &rules);
            println!("Simplified {} = {}", carry, carry_expr_egg);
        }
        use Boolexpr::*;
        if let Some(c1) = m.get(&Var("carry_1".to_string(), false)) {
            if let Some(c2) = m.get(&Var("carry_2".to_string(), false)) {
                // rules.push(rw!("carry-subst"; "carry_1" => "(& (~ x) old_carry_1)"));
                let carry2 = subst_vars((*c2).clone(), &m);
                println!("After substitution: {}", carry2);
                let carry_r = BinExpr(BoolBinOp::Xor, Box::new(c1.clone()), Box::new(UniExpr(BoolUniOp::Not, Box::new(carry2))));
                let carry_egg = egg_simp(carry_r.mk_string(true, false), &rules);
                println!("Simplified carry recursion from:\n\t{}\nTo:\n\t{}", carry_r, carry_egg);
            }
        }
    } else {
        println!("Got no carries");
    }
}

fn egg_rules() -> Vec<egg::Rewrite<egg::SymbolLang, ()>> {
    let rules: Vec<Rewrite<SymbolLang, ()>> = vec![ 
        rw!("commute-and"; "(& ?x ?y)" => "(& ?y ?x)"),
        rw!("commute-or";  "(| ?x ?y)" => "(| ?y ?x)"),
        rw!("commute-xor"; "(^ ?x ?y)" => "(^ ?y ?x)"),
        //    rw!("xor";         "(^ ?x ?y)" => "(& (| ?x ?y) (| (~ x) (~ y)))"),

        rw!("dist-or-and"; "(| ?x (& ?y ?z))" => "(& (| ?x ?y) (| ?x ?z))"),
        rw!("dist-and-or"; "(& ?x (| ?y ?z))" => "(| (& ?x ?y) (& ?x ?z))"),
        rw!("dist-xor-or"; "(^ ?x (| ?y ?z))" => "(| (& (~ ?x) (| ?y ?z)) (& ?x (& (~ ?y) (~ ?z))))"),
        rw!("dist-and-xor"; "(& ?x (^ ?y ?z))"=> "(^ (& ?x ?y) (& ?x ?z))"),

        rw!("assoc-xor"; "(^ ?x (^ ?y ?z))"=> "(^ (^ ?x ?y) ?z)"),

        rw!("demorgan-and"; "(~ (& ?x ?y))" => "(| (~ ?y) (~ ?x))"),
        rw!("demorgan-or";  "(~ (| ?x ?y))" => "(& (~ ?y) (~ ?x))"),
        
        rw!("and-false"; "(& ?x false)" => "false"),
        rw!("and-true"; "(& ?x true)" => "?x"),
        rw!("and-self"; "(& ?x ?x)" => "?x"),
        rw!("and-self-neg"; "(& ?x (~ ?x))" => "false"),
        
        rw!("or-false";  "(| ?x false)" => "?x"),
        rw!("or-true";  "(| ?x true)" => "true"),
        rw!("or-self";  "(| ?x ?x)" => "?x"),
        rw!("or-self-neg";  "(| ?x (~ ?x))" => "true"),
        rw!("xor-false"; "(^ ?x false)" => "?x"),
        rw!("xor-true"; "(^ ?x true)" => "(~ ?x)"),
        rw!("xor-self";   "(^ ?x ?x)" => "false"),
        rw!("xor-self-neg"; "(^ ?x (~ ?x))" => "true"),
        rw!("neg-dbl"; "(~ (~ ?x))" => "?x"),
    ];
    rules
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
        //    rw!("and-false"; "(& ?x false)" => "false"),
        //    rw!("and-true"; "(& ?x true)" => "?x"),
        //    rw!("and-self"; "(& ?x ?x)" => "?x"),
        //    rw!("and-self-neg"; "(& ?x (~ ?x))" => "false"),
        //
        //    rw!("or-false";  "(| ?x false)" => "?x"),
        //    rw!("or-true";  "(| ?x true)" => "true"),
        //    rw!("or-self";  "(| ?x ?x)" => "?x"),
        //    rw!("or-self-neg";  "(| ?x (~ ?x))" => "true"),
        rw!("xor-false"; "(^ ?x false)" => "?x"),
        rw!("xor-true"; "(^ ?x true)" => "(~ ?x)"),
        rw!("xor-self";   "(^ ?x ?x)" => "false"),
        rw!("xor-self-neg"; "(^ ?x (~ ?x))" => "true"),
        rw!("neg-dbl"; "(~ (~ ?x))" => "?x"),
    ];

    // While it may look like we are working with numbers,
    // SymbolLang stores everything as strings.
    // We can make our own Language later to work with other types.
    //let start = "(| true (& true true))".parse().unwrap();
    let start = "(^ x (^ (^ (~ x) (^ false carry_3)) carry_5))"
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

fn egg_simp(s:String, rules: &[Rewrite<SymbolLang, ()>]) -> egg::RecExpr<egg::SymbolLang> {
    let start = s.parse().unwrap();
    let runner = Runner::default().with_expr(&start).run(rules);
    let mut extractor = Extractor::new(&runner.egraph, AstSize);
    let (_best_cost, best_expr) = extractor.find_best(runner.roots[0]);
    best_expr
}


fn main() {
    println!("Hello, world!");

    //egg_test();
    simple_example();

    println!("Done!");
}
