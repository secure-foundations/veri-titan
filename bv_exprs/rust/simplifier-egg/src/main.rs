#![allow(dead_code)]

use egg::{rewrite as rw, *};
use std::collections::HashMap;
use std::collections::HashSet;
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

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy, PartialOrd, Ord)]
enum BoolBinOp {
    And,
    Or,
    Xor,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy, PartialOrd, Ord)]
enum BoolUniOp {
    Not,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, PartialOrd, Ord)]
enum BoolExpr_ {
    Const(bool),
    Var(String, bool),
    UniExpr(BoolUniOp, BoolExpr),
    BinExpr(BoolBinOp, BoolExpr, BoolExpr),
}
type BoolExpr = Rc<BoolExpr_>;

struct Namer {
    ctr: u32,
}

impl Namer {
    pub fn new() -> Namer {
        Namer { ctr: 0 }
    }

    fn get_name(&mut self, s: &str) -> String {
        self.ctr = self.ctr + 1;
        format!("{}_{}", s, self.ctr)
    }

    fn reset(&mut self) {
        self.ctr = 0;
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
enum StrMode {
    Infix,
    Prefix,
    Dafny,
    DafnyFunction(String),
}

impl BoolExpr_ {
    fn mk_string(&self, mode: &StrMode, age_carries: bool) -> String {
        use BoolExpr_::*;
        use StrMode::*;
        match &*self {
            Const(c) => format!("{}", c),
            Var(v, old) => {
                let s = if *old {
                    format!("old_{}", v)
                } else {
                    format!("{}", v)
                };
                match mode {
                    DafnyFunction(i) => match &v.find("carry") {
                        None => format!("{}({})", s, i),
                        Some(_) => {
                            if age_carries {
                                format!("{}({}-1)", s, i)
                            } else {
                                format!("{}({})", s, i)
                            }
                        }
                    },
                    _ => s,
                }
            }
            UniExpr(op, src) => {
                let BoolUniOp::Not = *op;
                let src = (*src).mk_string(mode, age_carries);
                match mode {
                    Infix => format!("~{}", src),
                    Prefix => format!("(~ {})", src),
                    Dafny | DafnyFunction(_) => format!("!{}", src),
                }
            }
            BinExpr(op, src0, src1) => {
                use BoolBinOp::*;
                let s0 = src0.mk_string(mode, age_carries);
                let s1 = src1.mk_string(mode, age_carries);
                let normal_op_str = match op {
                    And => "&",
                    Or => "|",
                    Xor => "^",
                };
                match mode {
                    Infix => format!("({} {} {})", s0, normal_op_str, s1),
                    Prefix => format!("({} {} {})", normal_op_str, s0, s1),
                    Dafny | DafnyFunction(_) => match op {
                        And => format!("({} && {})", s0, s1),
                        Or => format!("({} || {})", s0, s1),
                        Xor => format!("xor({}, {})", s0, s1),
                    },
                }
            }
        }
    }

    fn age_carries(&self) -> BoolExpr {
        use BoolExpr_::*;
        match self {
            Const(_) => self.clone().into(),
            Var(name, old) => {
                if !old {
                    match &name.find("carry") {
                        None => self.clone().into(),
                        Some(_) => Var((*name).clone(), true).into(),
                    }
                } else {
                    self.clone().into()
                }
            }
            UniExpr(op, src) => UniExpr(*op, src.age_carries()).into(),
            BinExpr(op, src0, src1) => {
                let src0 = src0.age_carries();
                let src1 = src1.age_carries();
                BinExpr(*op, src0, src1).into()
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
}

impl fmt::Display for BoolExpr_ {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.mk_string(&StrMode::Infix, true))
    }
}

impl BVExpr_ {
    /*
    fn get_bit_exprs(&self, n: &mut Namer) -> (BoolExpr, HashMap<BoolExpr, BoolExpr>) {
        use BoolBinOp::*;
        use BoolExpr_::*;
        match self {
            BVExpr_::Const(_c) => (Const(false).into(), Default::default()),
            BVExpr_::Var(v) => (Var(v.clone(), false).into(), Default::default()),
            BVExpr_::UniExpr(op, src) => {
                let BVUniOp::Neg = *op;
                let (src, map) = src.get_bit_exprs(n);
                (UniExpr(BoolUniOp::Not, src).into(), map)
            }
            BVExpr_::BinExpr(op, src0, src1) => {
                let (src0, map0) = src0.get_bit_exprs(n);
                let (src1, map1) = src1.get_bit_exprs(n);
                let maps = map0.into_iter().chain(map1.into_iter()).collect();
                match op {
                    BVBinOp::And => (BinExpr(And, src0, src1).into(), maps),
                    BVBinOp::Or => (BinExpr(Or, src0, src1).into(), maps),
                    BVBinOp::Xor => (BinExpr(Xor, src0, src1).into(), maps),
                    BVBinOp::Add => {
                        let carry_name = n.get_name("carry");
                        let carry_var: BoolExpr = Var(carry_name.clone(), false).into();
                        let carry_expr = BinExpr(
                            Or,
                            BinExpr(And, src0.clone(), src1.clone()).into(),
                            BinExpr(
                                And,
                                carry_var.clone(),
                                BinExpr(Or, src0.clone(), src1.clone()).into(),
                            )
                            .into(),
                        )
                        .into();
                        let mut maps = maps;
                        maps.insert(carry_var.clone(), carry_expr);
                        let add_expr =
                            BinExpr(Xor, src0, BinExpr(Xor, src1, carry_var).into()).into();
                        (add_expr, maps)
                    }
                    BVBinOp::Sub => unreachable!(),
                }
            }
        }
    }
    */

    fn simp(&self) -> BVExpr {
        use BVExpr_::*;
        match self {
            Const(_) | Var(_) => self.clone().into(),
            UniExpr(op, src) => UniExpr(*op, src.simp()).into(),
            BinExpr(op, src0, src1) => {
                let src0 = src0.simp();
                let src1 = src1.simp();
                match op {
                    BVBinOp::Sub => BinExpr(
                        BVBinOp::Add,
                        src0,
                        BinExpr(
                            BVBinOp::Add,
                            UniExpr(BVUniOp::Neg, src1).into(),
                            Const(1).into(),
                        )
                        .into(),
                    )
                    .into(),
                    _ => BinExpr(*op, src0, src1).into(),
                }
            }
        }
    }

    fn dafny_decl_vars(&self, vars: &mut HashSet<String>) -> String {
        use BVExpr_::*;
        match self {
            Const(_) => "".into(),
            Var(name) => {
                match &name.find("carry") {
                    None => {
                        if !vars.contains(name) {
                            // Declare an uninterpreted function representing this variable
                            vars.insert(name.clone());
                            format!("function {}(i:nat) : bool\n", name)
                        } else {
                            "".into()
                        }
                    }
                    Some(_) => "".into(),
                }
            }
            UniExpr(_, src) => src.dafny_decl_vars(vars),
            BinExpr(_, src0, src1) => format!(
                "{}{}",
                src0.dafny_decl_vars(vars),
                src1.dafny_decl_vars(vars)
            ),
        }
    }

    fn get_main_bit_expr(&self, n: &mut Namer, base_case: bool) -> BoolExpr {
        use BoolBinOp::*;
        use BoolExpr_::*;
        match self {
            BVExpr_::Const(c) => {
                if base_case {
                    // result depends on value of the constant
                    if *c == 0 {
                        Const(false).into()
                    } else {
                        Const(true).into()
                    }
                } else {
                    // Otherwise, b/c we only support 0 and 1, the upper bits are always 0
                    Const(false).into()
                }
            }
            BVExpr_::Var(v) => Var(v.clone(), false).into(),
            BVExpr_::UniExpr(op, src) => {
                let BVUniOp::Neg = *op;
                let src = src.get_main_bit_expr(n, base_case);
                UniExpr(BoolUniOp::Not, src).into()
            }
            BVExpr_::BinExpr(op, src0, src1) => {
                let src0 = src0.get_main_bit_expr(n, base_case);
                let src1 = src1.get_main_bit_expr(n, base_case);
                match op {
                    BVBinOp::And => BinExpr(And, src0, src1).into(),
                    BVBinOp::Or => BinExpr(Or, src0, src1).into(),
                    BVBinOp::Xor => BinExpr(Xor, src0, src1).into(),
                    BVBinOp::Add => {
                        if base_case {
                            // No incoming carry
                            BinExpr(Xor, src0, src1).into()
                        } else {
                            let carry_name = n.get_name("carry");
                            let carry_var: BoolExpr = Var(carry_name.clone(), false).into();
                            BinExpr(Xor, src0, BinExpr(Xor, src1, carry_var).into()).into()
                        }
                    }
                    BVBinOp::Sub => unreachable!(),
                }
            }
        }
    }

    fn get_carry_exprs(
        &self,
        n: &mut Namer,
        base_case: bool,
        carries: &mut HashMap<BoolExpr, BoolExpr>,
    ) {
        use BoolBinOp::*;
        use BoolExpr_::*;
        match self {
            BVExpr_::Const(_) | BVExpr_::Var(_) => (),
            BVExpr_::UniExpr(_, src) => src.get_carry_exprs(n, base_case, carries),
            BVExpr_::BinExpr(op, src0, src1) => {
                let orig_ctr = n.ctr;
                src0.get_carry_exprs(n, base_case, carries);
                src1.get_carry_exprs(n, base_case, carries);
                let final_ctr = n.ctr;
                n.ctr = orig_ctr; // Need to keep numbering of the main bit consistent
                let s0 = src0.get_main_bit_expr(n, base_case);
                let s1 = src1.get_main_bit_expr(n, base_case);
                n.ctr = final_ctr;
                match op {
                    BVBinOp::And | BVBinOp::Or | BVBinOp::Xor => (),
                    BVBinOp::Add => {
                        let carry_name = n.get_name("carry");
                        let carry_var: BoolExpr = Var(carry_name.clone(), false).into();
                        let carry_expr = if base_case {
                            // No incoming carry
                            BinExpr(And, s0.clone(), s1.clone()).into()
                        } else {
                            BinExpr(
                                Or,
                                BinExpr(And, s0.clone(), s1.clone()).into(),
                                BinExpr(
                                    And,
                                    carry_var.clone(),
                                    BinExpr(Or, s0.clone(), s1.clone()).into(),
                                )
                                .into(),
                            )
                            .into()
                        };
                        carries.insert(carry_var.clone(), carry_expr);
                    }
                    BVBinOp::Sub => unreachable!(),
                }
            }
        }
    }
}

fn identity() -> BVExpr {
    use BVBinOp::*;
    use BVExpr_::*;

    // x - x
    let x: BVExpr = Var("x".to_owned()).into();
    BinExpr(Sub, x.clone(), x).into()
}

fn identity2() -> BVExpr {
    use BVBinOp::*;
    use BVExpr_::*;

    // x - (x + (x - x))
    let x: BVExpr = Var("x".to_owned()).into();
    BinExpr(
        Sub,
        x.clone(),
        BinExpr(Add, x.clone(), BinExpr(Sub, x.clone(), x).into()).into(),
    )
    .into()
}

fn addsub_1043() -> BVExpr {
    use BVBinOp::*;
    use BVExpr_::*;

    // ((x & y) ^ y) + 1 + (x | ~y)
    let x: BVExpr = Var("x".to_owned()).into();
    let y: BVExpr = Var("y".to_owned()).into();
    BinExpr(
        Add,
        BinExpr(Xor, BinExpr(And, x.clone(), y.clone()).into(), y.clone()).into(),
        BinExpr(
            Add,
            Const(1).into(),
            BinExpr(Or, x, UniExpr(BVUniOp::Neg, y).into()).into(),
        )
        .into(),
    )
    .into()
}

fn test() {
    let f = identity();
    let f = f.simp();
    println!("{}", f);
    let mut namer = Namer::new();
    //let (f_generic_bit, carries) = f.get_bit_exprs(&mut namer);
    //namer.reset();
    let f_base_bit = f.get_main_bit_expr(&mut namer, true);
    namer.reset();
    let f_generic_bit2 = f.get_main_bit_expr(&mut namer, false);
    //println!("Original: {}\nNew:      {}\nBase: {}", f_generic_bit, f_generic_bit2, f_base_bit);
    println!("New:      {}\nBase: {}", f_generic_bit2, f_base_bit);

    //    println!("\nOriginal carries:");
    //    for (carry, carry_expr) in carries.iter() {
    //        println!("{} = {}", carry, carry_expr);
    //    }
    //
    let mut new_carries = Default::default();
    namer.reset();
    f.get_carry_exprs(&mut namer, false, &mut new_carries);

    println!("\nNew carries:");
    for (carry, carry_expr) in new_carries.iter() {
        println!("{} = {}", carry, carry_expr);
    }

    let mut base_carries = Default::default();
    namer.reset();
    f.get_carry_exprs(&mut namer, true, &mut base_carries);

    println!("\nBase carries:");
    for (carry, carry_expr) in base_carries.iter() {
        println!("{} = {}", carry, carry_expr);
    }
}

fn print_dafny() {
    // Define xor
    println!(
        "
function xor(x:bool, y:bool) : bool {{
    (x || y) && (!x || !y)
}}
"
    );

    //let f = identity();
    //let f = identity2();
    let f = addsub_1043();
    let f = f.simp();
    let mut namer = Namer::new();
    let f_base_bit = f.get_main_bit_expr(&mut namer, true);
    namer.reset();
    let f_generic_bit = f.get_main_bit_expr(&mut namer, false);

    let mut vars = HashSet::new();
    println!("{}", f.dafny_decl_vars(&mut vars));

    // Declare the main function
    println!(
        "
function bit(i:nat) : bool {{
    if i == 0 then {}
    else {}
}}\n",
        f_base_bit.mk_string(&StrMode::DafnyFunction("0".to_string()), true),
        f_generic_bit.mk_string(&StrMode::DafnyFunction("i".to_string()), true)
    );

    namer.reset();
    let mut carries_base = Default::default();
    f.get_carry_exprs(&mut namer, true, &mut carries_base);

    namer.reset();
    let mut carries_generic = Default::default();
    f.get_carry_exprs(&mut namer, false, &mut carries_generic);

    // Declare the carry functions
    // TODO: Consider using egg to simplify the expressions first
    for (carry, carry_expr) in carries_generic.iter() {
        if let BoolExpr_::Var(name, _old) = &**carry {
            if let Some(base_expr) = carries_base.get(carry) {
                let base = base_expr.mk_string(&StrMode::DafnyFunction("0".to_string()), true);
                let generic = carry_expr.mk_string(&StrMode::DafnyFunction("i".to_string()), true);
                println!(
                    "
function {}(i:nat) : bool {{
    if i == 0 then {}
    else {}
}}\n",
                    name, base, generic
                );
            }
        }
    }

    // Find the recurrsion relation
    let rules = egg_rules();
    //let f_egg = egg_simp(f_generic_bit.mk_string(&StrMode::Prefix), &rules);
    let f_egg = egg_simp_to_bool_expr(f_generic_bit.mk_string(&StrMode::Prefix, true), &rules);
    eprintln!("Original: {}\nSimplified: {}", f_generic_bit.mk_string(&StrMode::Prefix, true), f_egg);
    let f_egg_i = f_egg.mk_string(&StrMode::DafnyFunction("i".to_string()), false);
    let f_egg_i_minus_1 = f_egg.mk_string(&StrMode::DafnyFunction("i".to_string()), true);
    let f_egg_base = f_egg.mk_string(&StrMode::DafnyFunction("0".to_string()), false);

    // Print the verification lemma
    println!(
        "
lemma function_test(i:nat)
    // Sanity check base case\n
    ensures bit(0) == false
    ensures {} == false;

    // Induction hypothesis
    ensures i > 0 ==> bit(i) == {};
    ensures i > 0 ==> {} == {};

    // Conclusion
    ensures bit(i) == false
{{
}}
",
        f_egg_base, f_egg_i_minus_1, f_egg_i, f_egg_i_minus_1
    );
}

fn simple_example() {
    let f = identity();
    //let f = identity2();
    println!("Original BV expr: {}", f);
    let f = f.simp();
    println!("Simplified BV expr: {}", f);

    let mut namer = Namer::new();
    //let (f_expr, carries) = f.get_bit_exprs(&mut namer);
    let f_expr = f.get_main_bit_expr(&mut namer, false);

    namer.reset();
    let mut carries_generic = Default::default();
    f.get_carry_exprs(&mut namer, false, &mut carries_generic);

    namer.reset();
    println!("Main bool expr: {}", f_expr);
    println!(
        "Main bool expr infix: {}",
        f_expr.mk_string(&StrMode::Prefix, true)
    );
    println!(
        "Main bool expr DafnyFunction: {}",
        f_expr.mk_string(&StrMode::DafnyFunction("i".to_string()), true)
    );
    println!(
        "Main bool expr base: {}",
        f.get_main_bit_expr(&mut namer, true)
            .mk_string(&StrMode::DafnyFunction("i".to_string()), true)
    );

    let rules = egg_rules();
    let f_egg = egg_simp(f_expr.mk_string(&StrMode::Prefix, true), &rules);
    println!("Main bool expr simplified: {}", f_egg);

    for (carry, carry_expr) in carries_generic.iter() {
        println!("{} = {}", carry, carry_expr);
        //        let carry_expr_egg = egg_simp(carry_expr.mk_string(&StrMode::Prefix), &rules);
        //        println!("Simplified {} = {}", carry, carry_expr_egg);
    }
    /*
    use BoolExpr_::*;
    if let Some(c1) = carries.get((&Var("carry_1".to_string(), false)).into()) {
        if let Some(c2) = carries.get((&Var("carry_2".to_string(), false)).into()) {
            // rules.push(rw!("carry-subst"; "carry_1" => "(& (~ x) old_carry_1)"));
            let carry2 = c2.age_carries();
            println!("After aging, carry2 = {}", carry2);
            let carry_r: BoolExpr = BinExpr(
                BoolBinOp::Xor,
                c1.clone(),
                UniExpr(BoolUniOp::Not, carry2).into(),
            )
            .into();
            let carry_egg = egg_simp(carry_r.mk_string(true, false), &rules);
            println!(
                "Simplified carry recursion from:\n\t{}\nTo:\n\t{}",
                carry_r, carry_egg
            );
        }
    }
    */
}

// Define an egg language
define_language! {
    enum BoolLanguage {
        "true" = True,
        "false" = False,
        "~" = Not(Id),
        "^" = Xor([Id; 2]),
        "&" = And([Id; 2]),
        "|" =  Or([Id; 2]),
        Symbol(Symbol),
    }
}

fn bool_expr_to_lang(e: BoolExpr) -> RecExpr<BoolLanguage> {
    e.mk_string(&StrMode::Prefix, true).parse().unwrap()
}

fn bool_lang_to_expr(nodes: &[BoolLanguage], enode: &BoolLanguage) -> BoolExpr {
    use BoolExpr_::*;
    use BoolLanguage::*;
    //let nodes = &enode.as_ref();
    //let enode = nodes[nodes.len()-1];
    let expr_ = match enode {
        True => Const(true),
        False => Const(false),
        Not(c) => UniExpr(
            BoolUniOp::Not,
            bool_lang_to_expr(nodes, &nodes[usize::from(*c)]).into(),
        ),
        Xor([c0, c1]) => BinExpr(
            BoolBinOp::Xor,
            bool_lang_to_expr(nodes, &nodes[usize::from(*c0)]).into(),
            bool_lang_to_expr(nodes, &nodes[usize::from(*c1)]).into(),
        ),
        And([c0, c1]) => BinExpr(
            BoolBinOp::And,
            bool_lang_to_expr(nodes, &nodes[usize::from(*c0)]).into(),
            bool_lang_to_expr(nodes, &nodes[usize::from(*c1)]).into(),
        ),
        Or([c0, c1]) => BinExpr(
            BoolBinOp::Or,
            bool_lang_to_expr(nodes, &nodes[usize::from(*c0)]).into(),
            bool_lang_to_expr(nodes, &nodes[usize::from(*c1)]).into(),
        ),
        Symbol(s) => Var(s.to_string(), false),
    };
    expr_.into()
}

fn egg_rules() -> Vec<egg::Rewrite<BoolLanguage, ()>> {
    let rules: Vec<Rewrite<BoolLanguage, ()>> = vec![
        rw!("commute-and"; "(& ?x ?y)" => "(& ?y ?x)"),
        rw!("commute-or";  "(| ?x ?y)" => "(| ?y ?x)"),
        rw!("commute-xor"; "(^ ?x ?y)" => "(^ ?y ?x)"),

        rw!("xor-def";     "(^ ?x ?y)" => "(& (| ?x ?y) (| (~ ?x) (~ ?y)))"),
        rw!("xor-def-rev"; "(& (| ?x ?y) (| (~ ?x) (~ ?y)))" => "(^ ?x ?y)"),

        rw!("dist-or-and-1"; "(| ?x (& ?y ?z))" => "(& (| ?x ?y) (| ?x ?z))"),
        rw!("dist-or-and-2"; "(& (| ?x ?y) (| ?x ?z))" => "(| ?x (& ?y ?z))"),

        rw!("dist-and-or-1"; "(& ?x (| ?y ?z))" => "(| (& ?x ?y) (& ?x ?z))"),
        rw!("dist-and-or-2"; "(| (& ?x ?y) (& ?x ?z))" => "(& ?x (| ?y ?z))"),

        rw!("dist-xor-or-1"; "(^ ?x (| ?y ?z))" => "(| (& (~ ?x) (| ?y ?z)) (& ?x (& (~ ?y) (~ ?z))))"),
        rw!("dist-xor-or-2"; "(| (& (~ ?x) (| ?y ?z)) (& ?x (& (~ ?y) (~ ?z))))" => "(^ ?x (| ?y ?z))"),

        rw!("dist-and-xor-1"; "(& ?x (^ ?y ?z))" => "(^ (& ?x ?y) (& ?x ?z))"),
        rw!("dist-and-xor-2"; "(^ (& ?x ?y) (& ?x ?z))" => "(& ?x (^ ?y ?z))"),

        rw!("dist-xor-and-1"; "(^ ?x (& ?y ?z))" => "(| (& (~ ?x) (& ?y ?z)) (& ?x (~ (& ?y ?z))))"),
        rw!("dist-xor-and-1"; "(^ ?x (| ?y ?z))" => "(| (& (~ ?x) (| ?y ?z)) (& ?x (~ (| ?y ?z))))"),

        rw!("assoc-xor-1"; "(^ ?x (^ ?y ?z))" => "(^ (^ ?x ?y) ?z)"),
        rw!("assoc-xor-2"; "(^ (^ ?x ?y) ?z)" => "(^ ?x (^ ?y ?z))"),

        rw!("assoc-and-1"; "(& ?x (& ?y ?z))" => "(& (& ?x ?y) ?z)"),
        rw!("assoc-and-2"; "(& (& ?x ?y) ?z)" => "(& ?x (& ?y ?z))"),

        rw!("assoc-or-1"; "(| ?x (| ?y ?z))" => "(| (| ?x ?y) ?z)"),
        rw!("assoc-or-2"; "(| (| ?x ?y) ?z)" => "(| ?x (| ?y ?z))"),

        rw!("demorgan-and-1"; "(~ (& ?x ?y))" => "(| (~ ?x) (~ ?y))"),
        rw!("demorgan-and-2"; "(| (~ ?x) (~ ?y))" => "(~ (& ?x ?y))"),

        rw!("demorgan-or-1"; "(~ (| ?x ?y))" => "(& (~ ?x) (~ ?y))"),
        rw!("demorgan-or-2"; "(& (~ ?x) (~ ?y))" => "(~ (| ?x ?y))"),

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
//        //    rw!("commute-and"; "(& ?x ?y)" => "(& ?y ?x)"),
//        //    rw!("commute-or";  "(| ?x ?y)" => "(| ?y ?x)"),
//        rw!("commute-xor"; "(^ ?x ?y)" => "(^ ?y ?x)"),
//        //    rw!("xor";         "(^ ?x ?y)" => "(& (| ?x ?y) (| (~ x) (~ y)))"),
//
//        //    rw!("dist-or-and"; "(| ?x (& ?y ?z))" => "(& (| ?x ?y) (| ?x ?z))"),
//        //    rw!("dist-and-or"; "(& ?x (| ?y ?z))" => "(| (& ?x ?y) (& ?x ?z))"),
//        //    rw!("dist-xor-or"; "(^ ?x (| ?y ?z))" => "(| (& (~ ?x) (| ?y ?z)) (& ?x (& (~ y) (~ z))))"),
//        //    rw!("dist-and-xor"; "(& ?x (^ ?y ?z))"=> "(^ (& ?x ?y) (& ?x ?z))"),
//        rw!("assoc-xor"; "(^ ?x (^ ?y ?z))"=> "(^ (^ ?x ?y) ?z)"),
//        //
//        //
//        //    rw!("demorgan"; "(~ (^ ?x ?y))" => "(| (~ ?y) (~ ?x))"),
//        //
//        //    rw!("and-false"; "(& ?x false)" => "false"),
//        //    rw!("and-true"; "(& ?x true)" => "?x"),
//        //    rw!("and-self"; "(& ?x ?x)" => "?x"),
//        //    rw!("and-self-neg"; "(& ?x (~ ?x))" => "false"),
//        //
//        //    rw!("or-false";  "(| ?x false)" => "?x"),
//        //    rw!("or-true";  "(| ?x true)" => "true"),
//        //    rw!("or-self";  "(| ?x ?x)" => "?x"),
//        //    rw!("or-self-neg";  "(| ?x (~ ?x))" => "true"),
//        rw!("xor-false"; "(^ ?x false)" => "?x"),
        rw!("xor-true"; "(^ ?x true)" => "(~ ?x)"),
//        rw!("xor-self";   "(^ ?x ?x)" => "false"),
        rw!("xor-self-neg"; "(^ ?x (~ ?x))" => "true"),
//        rw!("neg-dbl"; "(~ (~ ?x))" => "?x"),
        rw!("assoc-xor1"; "(^ ?x (^ ?y ?z))"=> "(^ (^ ?x ?y) ?z)"),
//        rw!("assoc-xor2"; "(^ (^ ?x ?y) ?z)"=> "(^ ?x (^ ?y ?z))"),
        //rw!("neg-dbl"; "(~ (~ ?x))" => "?x"),
    ];

    // While it may look like we are working with numbers,
    // SymbolLang stores everything as strings.
    // We can make our own Language later to work with other types.
    //let start = "(| true (& true true))".parse().unwrap();
    //let start = "(^ x (^ (^ (~ x) (^ false carry_3)) carry_5))"
    let start = "(^ (^ a b) (~ b))"
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

fn egg_simp(s: String, rules: &[Rewrite<BoolLanguage, ()>]) -> egg::RecExpr<BoolLanguage> {
    let start = s.parse().unwrap();
    let runner = Runner::default().with_expr(&start).run(rules);
    let mut extractor = Extractor::new(&runner.egraph, AstSize);
    let (_best_cost, best_expr) = extractor.find_best(runner.roots[0]);
    best_expr
}

fn egg_simp_to_bool_expr(s: String, rules: &[Rewrite<BoolLanguage, ()>]) -> BoolExpr {
    let start = s.parse().unwrap();
    let runner = Runner::default().with_expr(&start).run(rules);
    let mut extractor = Extractor::new(&runner.egraph, AstSize);
    let (_best_cost, best_expr) = extractor.find_best(runner.roots[0]);
    let nodes = best_expr.as_ref();
    let enode = &nodes[nodes.len() - 1];
    bool_lang_to_expr(nodes, &enode)
}

fn main() {
    //println!("Hello, world!");

    //egg_test();
    //simple_example();

    //test();

    //println!("\n\n");
    print_dafny();
    //egg_test();

    //println!("Done!");
}
