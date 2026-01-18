use egg::{rewrite as rw, *};
use std::{ops::Mul, sync::Arc};

define_language! {
    enum Math {
        Num(i32),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        Symbol(Symbol),
    }
}

type EGraph = egg::EGraph<Math, MinSize>;

// Our metadata in this case will be size of the smallest
// represented expression in the eclass.
#[derive(Default)]
struct MinSize;
impl Analysis<Math> for MinSize {
    type Data = usize;
    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_min(to, from)
    }
    fn make(egraph: &mut EGraph, enode: &Math, _id: Id) -> Self::Data {
        let get_size = |i: Id| egraph[i].data;
        AstSize.cost(enode, get_size)
    }
}

#[derive(Default)]
struct ConstantFold;
// do we need a primitive marker?
// const prim n => some prim n
impl Analysis<Math> for ConstantFold {
    type Data = Option<i32>;
    
    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        egg::merge_max(to, from)
    }

    fn make(egraph: &mut egg::EGraph<Math, ConstantFold>, enode: &Math, _id: Id) -> Self::Data {
        let x = |i: &Id| egraph[*i].data;
        match enode {
            Math::Num(n) => Some(*n),
            Math::Add([a, b]) => Some(x(a)? + x(b)?),
            Math::Mul([a, b]) => Some(x(a)? + x(b)?),
            _ => None,
        }
    }
}

fn mock_str_rewriter(s: &str) -> String {
    match s {
        "(* 5 (* 7 9))" => "(* 35 9)".to_string(),
       "(* 35 9)" => "315".to_string(),
        _ => s.to_string(),
    }
}

#[derive(Default)]
// mock analysis for function that computes constant folding as strings
struct ConstantFoldString;
impl Analysis<Math> for ConstantFoldString {
    type Data = Option<String>;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        egg::merge_max(to, from)
    }

    fn make(egraph: &mut egg::EGraph<Math, Self>, enode: &Math, _id: Id) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.clone();
        match enode {
            Math::Num(n) => Some(n.to_string()),
            Math::Add([a, b]) => Some(format!("(+ {} {})", x(a)?, x(b)?)),
            Math::Mul([a, b]) => Some(format!("(* {} {})", x(a)?, x(b)?)),
            _ => None,
        }
    }
}

// #[derive(Default)]
// struct MultiAnalysis {
//     min_size: MinSize,
//     constant_fold: ConstantFold,
// }

// impl Analysis<Math> for MultiAnalysis {
//     type Data = (usize, Option<i32>);  // Tuple of both data types
    
//     fn make(egraph: &mut egg::EGraph<Math, MultiAnalysis>, enode: &Math, id: Id) -> Self::Data {
//         let size = MinSize::make(egraph, enode, id);
//         let value = ConstantFold::make(egraph, enode, id);
//         (size, value)
//     }
    
//     fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
//         let m1 = self.min_size.merge(&mut to.0, from.0);
//         let m2 = self.constant_fold.merge(&mut to.1, from.1);
//         m1 | m2
//     }
// }


#[derive(Debug, Clone, PartialEq, Eq)]
struct Funky {
    a: Var,
    b: Var,
    c: Var,
    ast: PatternAst<Math>,
}

impl Applier<Math, MinSize> for Funky {

    fn apply_one(&self, egraph: &mut EGraph, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<Math>>, rule_name: Symbol) -> Vec<Id> {
        println!("a : {}, b : {}, c : {}", self.a, self.b, self.c);
        let a: Id = subst[self.a];
        // In a custom Applier, you can inspect the analysis data,
        // which is powerful combination!
        let size_of_a = egraph[a].data;
        if size_of_a > 50 {
            println!("Too big! Not doing anything");
            vec![]
        } else {
            // we're going to manually add:
            // (+ (+ ?a 0) (* (+ ?b 0) (+ ?c 0)))
            // to be unified with the original:
            // (+    ?a    (*    ?b       ?c   ))
            let b: Id = subst[self.b];
            let c: Id = subst[self.c];
            let zero = egraph.add(Math::Num(0));
            let a0 = egraph.add(Math::Add([a, zero]));
            let b0 = egraph.add(Math::Add([b, zero]));
            let c0 = egraph.add(Math::Add([c, zero]));
            let b0c0 = egraph.add(Math::Mul([b0, c0]));
            let a0b0c0 = egraph.add(Math::Add([a0, b0c0]));
            // Don't forget to union the new node with the matched node!
            if egraph.union_trusted(matched_id, a0b0c0, rule_name) {
                vec![a0b0c0]
            } else {
                vec![]
            }
        }
    }
}


fn main() {
    let rules = &[
        rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        rw!("add-0"; "(+ ?a 0)" => "?a"),
        rw!("mul-0"; "(* ?a 0)" => "0"),
        rw!("mul-1"; "(* ?a 1)" => "?a"),
        // the rewrite macro parses the rhs as a single token tree, so
        // we wrap it in braces (parens work too).
        rw!("funky"; "(+ ?a (* ?b ?c))" => { Funky {
            a: "?a".parse().unwrap(),
            b: "?b".parse().unwrap(),
            c: "?c".parse().unwrap(),
            ast: "(+ (+ ?a 0) (* (+ ?b 0) (+ ?c 0)))".parse().unwrap(),
        }}),
    ];
    println!("Test 1: Simple variables x, y, z");
    let start = "(+ x (* y z))".parse().unwrap();
    let end = "(+ (+ x 0) (* (+ y 0) (+ z 0)))".parse().unwrap();
    let mut runner = Runner::default().with_explanations_enabled().with_expr(&start).run(rules);
    let idk: Vec<String> = runner.explain_equivalence(&start, &end).make_flat_explanation()
    .iter()
    .map(|e| e.remove_rewrites().to_string())
    .collect();
    println!("{}", idk.join("\n"));
    
    println!("\n\nTest 2: Complex expressions (+ x 1), (+ y 2), (+ z 4)");
    let start2 = "(+ (+ x 1) (* (+ y 2) (+ z 4)))".parse().unwrap();
    // Expected pattern: (+ (+ ?a 0) (* (+ ?b 0) (+ ?c 0)))
    // Where ?a = (+ x 1), ?b = (+ y 2), ?c = (+ z 4)
    let end2 = "(+ (+ (+ x 1) 0) (* (+ (+ y 2) 0) (+ (+ z 4) 0)))".parse().unwrap();
    let mut runner2 = Runner::default().with_explanations_enabled().with_expr(&start2).run(rules);
    let idk2: Vec<String> = runner2.explain_equivalence(&start2, &end2).make_flat_explanation()
    .iter()
    .map(|e| e.remove_rewrites().to_string())
    .collect();
    println!("{}", idk2.join("\n"));
    
}

