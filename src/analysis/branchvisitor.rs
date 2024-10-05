use super::callback::get_span_string;
use regex::Regex;
use rustc_ast::{
    ptr::P,
    visit::{self, Visitor as ASTVisitor},
};
use rustc_hir::intravisit::{self, Visitor as HIRVisitor};
use rustc_middle::ty::TyCtxt;
use rustc_span::sym::format;
use thin_vec::ThinVec;

pub struct HIRBranchVisitor<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> HIRVisitor<'tcx> for HIRBranchVisitor<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx rustc_hir::Expr<'tcx>) -> Self::Result {
        match &ex.kind {
            rustc_hir::ExprKind::If(_, _, _) => {
                // Do something with the if expression
                println!("If expression found");
                // println!("{:#?}", ex);
            }
            rustc_hir::ExprKind::Loop(_, _, _, _) => {
                // Do something with the loop expression
                println!("Loop expression found");
                // println!("{:#?}", ex);
            }
            rustc_hir::ExprKind::Match(_, _, _) => {
                // Do something with the match expression
                println!("Match expression found");
                // println!("{:#?}", ex);
            }
            _ => {}
        }
        intravisit::walk_expr(self, ex);
    }
}

pub struct ASTBranchVisitor {
    re: Regex,
}

impl ASTBranchVisitor {
    pub fn new() -> Self {
        let re = Regex::new(r"^(.*?):(\d+):(\d+): (\d+):(\d+)").unwrap();
        Self { re }
    }

    fn get_string_from_span(&self, span: rustc_span::Span) -> String {
        let span_str = format!("{:?}", span);
        let caps = self.re.captures(&span_str).unwrap();

        let file_path = caps.get(1).map_or("", |m| m.as_str());
        let start_line = caps.get(2).map_or("", |m| m.as_str());
        let start_column = caps.get(3).map_or("", |m| m.as_str());
        let end_line = caps.get(4).map_or("", |m| m.as_str());
        let end_column = caps.get(5).map_or("", |m| m.as_str());

        // println!("File path: {}", file_path);
        // println!("Start: line {}, column {}", start_line, start_column);
        // println!("End: line {}, column {}", end_line, end_column);
        let res_str = get_span_string(
            file_path.to_string(),
            start_line.parse::<i32>().unwrap(),
            start_column.parse::<i32>().unwrap(),
            end_column.parse::<i32>().unwrap(),
        );
        println!("Condition: {}", res_str);
        res_str
    }

    fn handle_expr(&self, expr: &P<rustc_ast::Expr>) {
        match &expr.kind {
            rustc_ast::ExprKind::Binary(op, lexpr, rexpr) => {
                println!("Binary expression found");
                match &op.node {
                    rustc_ast::BinOpKind::And | rustc_ast::BinOpKind::Or => {
                        self.handle_expr(lexpr);
                        self.handle_expr(rexpr);
                    }
                    _ => {
                        self.get_string_from_span(expr.span);
                    }
                }
            }
            rustc_ast::ExprKind::Unary(op, subexpr) => {
                println!("Unary expression found");
                match &op {
                    rustc_ast::UnOp::Not => {
                        println!("Negation expression found");
                        self.handle_expr(subexpr);
                    }
                    _ => {
                        self.get_string_from_span(expr.span);
                    }
                }
            }
            rustc_ast::ExprKind::Let(pat, _, _, _) => {
                println!("Let expression found");
                self.get_string_from_span(pat.span);
            }
            rustc_ast::ExprKind::Paren(expr) => {
                self.handle_expr(expr);
            }
            _ => {
                self.get_string_from_span(expr.span);
            }
        }
    }

    fn handle_arms(&self, arms: &ThinVec<rustc_ast::Arm>) {
        for arm in arms {
            let pat_str = self.get_string_from_span(arm.pat.span);
            println!("Pattern: {}", pat_str);
            self.handle_pat(&arm.pat);
        }
    }

    fn handle_pat(&self, pat: &rustc_ast::Pat) {
        match &pat.kind {
            rustc_ast::PatKind::Or(subpats) => {
                for subpat in subpats {
                    self.handle_pat(subpat);
                }
            }
            rustc_ast::PatKind::Paren(subpat) => {
                self.handle_pat(subpat);
            }

            _ => {}
        }
    }
}

impl<'ast> ASTVisitor<'ast> for ASTBranchVisitor {
    fn visit_expr(&mut self, ex: &'ast rustc_ast::Expr) -> Self::Result {
        match &ex.kind {
            rustc_ast::ExprKind::If(cond_expr, _, _) => {
                // Do something with the if expression
                println!("If expression found");
                self.handle_expr(cond_expr);
                // println!("{:#?}", ex);
            }
            rustc_ast::ExprKind::While(cond_expr, _, _) => {
                // Do something with the while expression
                println!("While expression found");
                // println!("{:#?}", ex);
                self.handle_expr(cond_expr);
            }
            rustc_ast::ExprKind::ForLoop { pat, iter, .. } => {
                // Do something with the while expression
                println!("ForLoop expression found");
                // println!("{:#?}", ex);
                let pat_str = self.get_string_from_span(pat.span);
                let iter_str = self.get_string_from_span(iter.span);
                println!("{} in {}", pat_str, iter_str);
            }
            rustc_ast::ExprKind::Loop(_, _, _) => {
                // Do something with the loop expression
                println!("Loop expression found");
                // println!("{:#?}", ex);
            }
            rustc_ast::ExprKind::Match(match_expr, arms, _) => {
                // Do something with the match expression
                println!("Match expression found");
                // println!("{:#?}", ex);
                let match_str = self.get_string_from_span(match_expr.span);
                // self.handle_arms(arms);
                for arm in arms {
                    // let pat_str = self.get_string_from_span(arm.pat.span);
                    // println!("Pattern: {}", pat_str);
                    self.handle_pat(&arm.pat);
                }
            }
            _ => {}
        }
        visit::walk_expr(self, ex);
    }
}
