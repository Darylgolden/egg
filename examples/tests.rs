use egg::*;

define_language! {
    enum SimpleLanguage {
        Num(i32),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        Symbol(Symbol),
    }
}

fn make_rules() -> Vec<Rewrite<SimpleLanguage, ()>> {
    vec![
        rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("add-0"; "(+ ?a 0)" => "?a"),
        rewrite!("mul-0"; "(* ?a 0)" => "0"),
        rewrite!("mul-1"; "(* ?a 1)" => "?a"),
    ]
}

/// parse an expression, simplify it using egg, and pretty print it back out
fn simplify(s: &str, pattern_str: &str) -> String {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<SimpleLanguage> = s.parse().unwrap();

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let mut runner = Runner::default().with_expr(&expr).run(&make_rules());

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // let pat: Pattern<SimpleLanguage> = "(* ?x ?y)".parse().unwrap();
    // let matches = pat.search(&runner.egraph);
    // println!("{:?}", matches);
    // use an Extractor to pick the best element of the root eclass
    match_extract_rewrite(pattern_str, &mut runner.egraph);
    let return_stuff = match_and_extract(pattern_str, &runner.egraph);
    println!("{:#?}", return_stuff);
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);
    println!("Simplified {} to {} with cost {}", expr, best, best_cost);
    best.to_string()
}

fn match_extract_rewrite<L: Language + FromOp + std::fmt::Display, N: Analysis<L>>(pattern_str: &str, egraph: &mut EGraph<L, N>) {
    let matched_exprs = match_and_extract(pattern_str, egraph);
    expr_rewriter(matched_exprs, egraph);
}

fn match_and_extract<L: Language + FromOp + std::fmt::Display, N: Analysis<L>>(pattern_str: &str, egraph: &EGraph<L, N>) -> Vec<(String, Id)> {
    let extractor = Extractor::new(egraph, AstSize);
    let pat: Pattern<L> = pattern_str.parse().unwrap();
    let matches = pat.search(egraph);
    println!("Matches are {:?}", matches);
    let mut matched_exprs: Vec<(String, Id)> = Vec::new();
    for m in &matches {
        let eclass = m.eclass;
        let (best_cost, best) = extractor.find_best(eclass);
        println!("Found {} in eclass id {} with cost {}", best, eclass, best_cost);
        matched_exprs.push((best.to_string(), eclass));
    }   
    matched_exprs
}

fn expr_rewriter<L: Language + FromOp + std::fmt::Display, N: Analysis<L>>(
    matched_exprs: Vec<(String, Id)>, 
    egraph: &mut EGraph<L, N>) {
    for m in matched_exprs {
        let expr_str = m.0;
        let new_expr_str = mock_str_rewriter(&expr_str);
        let new_expr: RecExpr<L> = new_expr_str.parse().unwrap();
        let new_id = egraph.add_expr(&new_expr);
        egraph.union(m.1, new_id);
        egraph.rebuild();
    }
}

fn mock_str_rewriter(s: &str) -> String {
    match s {
        "(* 5 (* 7 9))" => "(* 35 9)".to_string(),
       "(* 35 9)" => "315".to_string(),
        _ => s.to_string(),
    }
}

fn main() {
    simplify("(* 5 (* 7 9))", "(* ?x ?y)");
}