use rustc_ast::{
    ptr::P,
    visit::{self, Visitor as ASTVisitor},
};
use rustc_hir::intravisit::{self, Visitor as HIRVisitor};
use rustc_middle::ty::TyCtxt;

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

pub struct ASTBranchVisitor {}

impl ASTBranchVisitor {
    fn handle_expr(&self, expr: &P<rustc_ast::Expr>) {
        match &expr.kind {
            // TODO: consider handling other binary operators, such as function calls
            rustc_ast::ExprKind::Binary(op, _, _) => {
                println!("Binary expression found");
                match &op.node {
                    rustc_ast::BinOpKind::And | rustc_ast::BinOpKind::Or => {
                        println!("Short-circuiting expression found");
                    }
                    _ => {}
                }
            }
            rustc_ast::ExprKind::Unary(op, _) => {
                println!("Unary expression found");
                match &op {
                    rustc_ast::UnOp::Not => {
                        println!("Negation expression found");
                    }
                    _ => {}
                }
            }
            rustc_ast::ExprKind::Let(pat, _, _, _) => {
                println!("Let expression found");
            }
            rustc_ast::ExprKind::Paren(expr) => {
                self.handle_expr(expr);
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
            rustc_ast::ExprKind::ForLoop {
                pat,
                iter,
                body,
                label,
                kind,
            } => {
                // Do something with the while expression
                println!("ForLoop expression found");
                // println!("{:#?}", ex);
            }
            rustc_ast::ExprKind::Loop(_, _, _) => {
                // Do something with the loop expression
                println!("Loop expression found");
                // println!("{:#?}", ex);
            }
            rustc_ast::ExprKind::Match(_, _, _) => {
                // Do something with the match expression
                println!("Match expression found");
                // println!("{:#?}", ex);
            }
            _ => {}
        }
        visit::walk_expr(self, ex);
    }
}
