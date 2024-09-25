use rustc_hir::intravisit::{self, Visitor as HIRVisitor};
use rustc_ast::visit::{self, Visitor as ASTVisitor};
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

pub struct ASTBranchVisitor {

}

impl<'ast> ASTVisitor<'ast> for ASTBranchVisitor {
    fn visit_expr(&mut self, ex: &'ast rustc_ast::Expr) -> Self::Result {
        match &ex.kind {
            rustc_ast::ExprKind::If(_, _, _) => {
                // Do something with the if expression
                println!("If expression found");
                // println!("{:#?}", ex);
            }
            rustc_ast::ExprKind::While(_, _, _) => {
                // Do something with the while expression
                println!("While expression found");
                // println!("{:#?}", ex);
            }
            rustc_ast::ExprKind::ForLoop { pat, iter, body, label, kind } => {
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