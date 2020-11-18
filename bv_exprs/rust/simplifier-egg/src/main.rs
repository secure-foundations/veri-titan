#![allow(dead_code)]

use egg::{*, rewrite as rw};
use std::collections::HashMap;
use std::fmt;
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

impl fmt::Display for BVExpr_ {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
enum BoolUniOp {
    Not,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
enum BoolExpr_ {
    Const(i64),
    Var(String,bool),
    UniExpr(BoolUniOp, BoolExpr),
    BinExpr(BoolBinOp, BoolExpr, BoolExpr),
}
type BoolExpr = Rc<BoolExpr_>;


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

impl BoolExpr_ {
    fn mk_string(&self, inline:bool, dafny:bool) -> String {
        use BoolExpr_::*;
        match &*self {
            Const(c) => format!("{}", c),
            Var(v,old) => 
                if *old {
                    format!("old_{}", v)
                } else {
                    format!("{}", v)
                }
            UniExpr(op, src) => {
                let BoolUniOp::Not = *op;
                let src = (*src).mk_string(inline, dafny);
                if inline {
                    format!("(~ {})", src)
                } else if dafny {
                    format!("!{}", src)
                } else {
                    format!("~{}", src)
                }
            },
            BinExpr(op, src0, src1) => {
                use BoolBinOp::*;
                let s0 = src0.mk_string(inline, dafny);
                let s1 = src1.mk_string(inline, dafny);
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

impl fmt::Display for BoolExpr_ {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.mk_string(false, true))
    }
}

impl BVExpr_ {
    fn get_bit_exprs(&self, n:& mut Namer) -> (BoolExpr, HashMap<BoolExpr, BoolExpr>) {
        use BoolExpr_::*;
        use BoolBinOp::*;
        match e {
            BVExpr::Const(_c) => (Const(false), None),
            BVExpr::Var(v) => (Var(v, false), None),
            BVExpr::UniExpr(op, src) => {
                let BVUniOp::Neg = *op;
                let (src, map) = src.get_bit_exprs(n);
                (UniExpr(BoolUniOp::Not, src).into(), map)
            }
            BVExpr::BinExpr(op, src0, src1) => {
                let (src0, map0) = src0.get_bit_exprs(n);
                let (src1, map1) = src1.get_bit_exprs(n);
                let maps = map0.into_iter().chain(map1.into_iter()).collect();
                match op {
                    BVBinOp::And => (BinExpr(And, src0, src1).into(), maps),
                    BVBinOp::Or => (BinExpr(Or, src0, src1).into(), maps),
                    BVBinOp::Xor => (BinExpr(Xor, src0, src1).into(), maps),
                    BVBinOp::Add => {
                        let carry_name = n.get_name("carry");
                        let carry_var = Var(carry_name.clone(), false).into();
                        let carry_Expr = BinExpr(
                            Or,
                            BinExpr(And, src0.clone(), src1.clone()).into(),
                            BinExpr(
                                And,
                                carry_var.clone(),
                                BinExpr(Or, src0.clone(), src1.clone()).into()).into(),
                        ).into();
                        let mut maps = maps;
                        maps.insert(carry_var.clone(), carry_expr);
                        let add_Expr = BinExpr(
                            Xor,
                            src0,
                            BinExpr(Xor, src1, carry_var).into()).into();
                        (add_Expr, maps)
                    }
                    BVBinOp::Sub => unreachable(),
                }
            }
        }
    }
}

/*


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

//fn subst_vars(e: Boolexpr, map:&HashMap<Boolexpr, Boolexpr>) -> Boolexpr {
//    use Boolexpr::*;
//    match &e {
//        Const(_) => e,
//        Var(_,old) => 
//            if !old {
//                match map.get(&e) {
//                    None => e,
//                    Some(rhs) => (*rhs).clone()
//                }
//            } else {
//                e
//            }
//        UniExpr(op, boxed_src) => UniExpr(*op, Box::new(subst_vars((**boxed_src).clone(), map))),
//        BinExpr(op, boxed_src0, boxed_src1) => {
//            let s0 = subst_vars((**boxed_src0).clone(), map);
//            let s1 = subst_vars((**boxed_src1).clone(), map);
//            BinExpr(*op, Box::new(s0), Box::new(s1))
//        }
//    }
//}

fn age_carries(e: Boolexpr) -> Boolexpr {
    use Boolexpr::*;
    match &e {
        Const(_) => e,
        Var(name,old) => 
            if !old {
                match &name.find("carry") {
                    None => e,
                    Some(_) => Var((*name).clone(), true)
                }
            } else {
                e
            }
        UniExpr(op, boxed_src) => UniExpr(*op, Box::new(age_carries((**boxed_src).clone()))),
        BinExpr(op, boxed_src0, boxed_src1) => {
            let s0 = age_carries((**boxed_src0).clone());
            let s1 = age_carries((**boxed_src1).clone());
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
                let carry2 = age_carries((*c2).clone());
                println!("After aging, carry2 = {}", carry2);
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

        rw!("demorgan-and"; "(~ (& ?x ?y))" => "(| (~ ?x) (~ ?y))"),
        rw!("demorgan-or";  "(~ (| ?x ?y))" => "(& (~ ?x) (~ ?y))"),
        
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
*/
