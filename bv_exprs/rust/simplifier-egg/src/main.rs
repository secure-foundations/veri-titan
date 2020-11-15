use std::collections::HashMap;
use egg::{*, rewrite as rw};

enum BVBinOp { And, Or, Xor, Add, Sub }
enum BVUniOp { Neg }

enum BVexpr {
    Const   ( i64 ),
    Var     ( String ),
    UniExpr ( BVUniOp, Box<BVexpr> ),
    BinExpr ( BVBinOp, Box<BVexpr>, Box<BVexpr> ),
}

enum BoolBinOp { And, Or, Xor }
enum BoolUniOp { Not }

enum Boolexpr {
    Const   ( i64 ),
    Var     ( String ),
    UniExpr ( BoolUniOp, Box<BVexpr> ),
    BinExpr ( BoolBinOp, Box<Boolexpr>, Box<Boolexpr> ),
}


fn get_bit_exprs(e:BVexpr) -> HashMap<Boolexpr,Boolexpr> {
    match e {
        Const(c) => 
        Var(v) =>
        UniExpr(op, boxed_src) => 
        BinExpr(op, boxed_src1, boxed_src1) => 
    }
}


fn identity() -> BVexpr {
    let x1 = Box::new(BVexpr::Var("x".to_owned()));
    let x2 = Box::new(BVexpr::Var("x".to_owned()));
    BVexpr::BinExpr(BVBinOp::Sub, x1, x2)
}

fn simple_example() {
    let f = identity();
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
    let start = "(^ x (^ (^ (~ x) (^ False carry_3)) carry_5))".parse().unwrap();

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
