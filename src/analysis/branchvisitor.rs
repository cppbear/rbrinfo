use super::callback::get_span_string;
use super::condition::{BoolCond, CmpIntKind, Condition, ForCond, MatchCond};
use regex::Regex;
use rustc_ast::{
    ptr::P,
    visit::{self, Visitor as ASTVisitor},
};
use rustc_hir::intravisit::{self, Visitor as HIRVisitor};
use rustc_middle::ty::TyCtxt;
use std::collections::BTreeMap;
// use thin_vec::ThinVec;

#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Ord)]
pub struct SourceInfo {
    pub file_path: String,
    pub start_line: i32,
    pub start_column: i32,
    pub end_line: i32,
    pub end_column: i32,
}

impl SourceInfo {
    pub fn contains(&self, other: &SourceInfo) -> bool {
        // Ensure the file paths are the same
        if self.file_path != other.file_path {
            return false;
        }

        // Check if the start position of `other` is after or at the start of `self`
        let start_within = (other.start_line > self.start_line)
            || (other.start_line == self.start_line && other.start_column >= self.start_column);

        // Check if the end position of `other` is before or at the end of `self`
        let end_within = (other.end_line < self.end_line)
            || (other.end_line == self.end_line && other.end_column <= self.end_column);

        start_within && end_within
    }

    pub fn expand(&self, other: &SourceInfo) -> Option<SourceInfo> {
        // Ensure the file paths are the same
        if self.file_path != other.file_path {
            return None;
        }

        // Determine the earliest start position
        let (start_line, start_column) = if (self.start_line < other.start_line)
            || (self.start_line == other.start_line && self.start_column <= other.start_column)
        {
            (self.start_line, self.start_column)
        } else {
            (other.start_line, other.start_column)
        };

        // Determine the latest end position
        let (end_line, end_column) = if (self.end_line > other.end_line)
            || (self.end_line == other.end_line && self.end_column >= other.end_column)
        {
            (self.end_line, self.end_column)
        } else {
            (other.end_line, other.end_column)
        };

        Some(SourceInfo {
            file_path: self.file_path.clone(),
            start_line,
            start_column,
            end_line,
            end_column,
        })
    }
}

pub struct HIRBranchVisitor<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> HIRVisitor<'tcx> for HIRBranchVisitor<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx rustc_hir::Expr<'tcx>) -> Self::Result {
        match &ex.kind {
            rustc_hir::ExprKind::If(_, _, _) => {
                // Do something with the if expression
                // println!("If expression found");
                // println!("{:#?}", ex);
            }
            rustc_hir::ExprKind::Loop(_, _, _, _) => {
                // Do something with the loop expression
                // println!("Loop expression found");
                // println!("{:#?}", ex);
            }
            rustc_hir::ExprKind::Match(_, _, _) => {
                // Do something with the match expression
                // println!("Match expression found");
                // println!("{:#?}", ex);
            }
            _ => {}
        }
        intravisit::walk_expr(self, ex);
    }
}

pub struct ASTBranchVisitor {
    re: Regex,
    cond_map: BTreeMap<SourceInfo, Condition>,
    pat_infos: Vec<(SourceInfo, String)>,
}

impl ASTBranchVisitor {
    pub fn new() -> Self {
        let re = Regex::new(r"^(.*?):(\d+):(\d+): (\d+):(\d+)").unwrap();
        Self {
            re,
            cond_map: BTreeMap::new(),
            pat_infos: Vec::new(),
        }
    }

    fn get_source_info(&self, span: rustc_span::Span) -> SourceInfo {
        let span_str = format!("{:?}", span);
        let caps = self.re.captures(&span_str).unwrap();

        let file_path = caps.get(1).map_or("", |m| m.as_str());
        let start_line = caps.get(2).map_or("", |m| m.as_str());
        let start_column = caps.get(3).map_or("", |m| m.as_str());
        let end_line = caps.get(4).map_or("", |m| m.as_str());
        let end_column = caps.get(5).map_or("", |m| m.as_str());

        SourceInfo {
            file_path: file_path.to_string(),
            start_line: start_line.parse::<i32>().unwrap(),
            start_column: start_column.parse::<i32>().unwrap(),
            end_line: end_line.parse::<i32>().unwrap(),
            end_column: end_column.parse::<i32>().unwrap(),
        }
    }

    fn get_string_from_span(&self, span: rustc_span::Span) -> String {
        let SourceInfo {
            file_path,
            start_line,
            start_column,
            end_column,
            ..
        } = self.get_source_info(span);

        // println!("File path: {}", file_path);
        // println!("Start: line {}, column {}", start_line, start_column);
        // println!("End: line {}, column {}", end_line, end_column);
        let res_str = get_span_string(file_path, start_line, start_column, end_column);
        res_str
    }

    fn handle_expr(&mut self, expr: &P<rustc_ast::Expr>) {
        match &expr.kind {
            rustc_ast::ExprKind::Binary(op, lexpr, rexpr) => {
                // println!("Binary expression found");
                match &op.node {
                    rustc_ast::BinOpKind::And | rustc_ast::BinOpKind::Or => {
                        self.handle_expr(lexpr);
                        self.handle_expr(rexpr);
                    }
                    rustc_ast::BinOpKind::Eq => {
                        let expr_str = self.get_string_from_span(expr.span);
                        let mut eq_with_int = false;
                        if let rustc_ast::ExprKind::Lit(lit) = &lexpr.kind {
                            if matches!(lit.kind, rustc_ast::token::LitKind::Integer) {
                                eq_with_int = true;
                            }
                        }
                        if let rustc_ast::ExprKind::Lit(lit) = &rexpr.kind {
                            if matches!(lit.kind, rustc_ast::token::LitKind::Integer) {
                                eq_with_int = true;
                            }
                        }
                        if eq_with_int {
                            let cond = Condition::Bool(BoolCond::new(expr_str, CmpIntKind::Eq));
                            self.cond_map.insert(self.get_source_info(expr.span), cond);
                        } else {
                            let cond = Condition::Bool(BoolCond::new(expr_str, CmpIntKind::No));
                            self.cond_map.insert(self.get_source_info(expr.span), cond);
                        }
                    }
                    rustc_ast::BinOpKind::Ne => {
                        let expr_str = self.get_string_from_span(expr.span);
                        let mut ne_with_int = false;
                        if let rustc_ast::ExprKind::Lit(lit) = &lexpr.kind {
                            if matches!(lit.kind, rustc_ast::token::LitKind::Integer) {
                                ne_with_int = true;
                            }
                        }
                        if let rustc_ast::ExprKind::Lit(lit) = &rexpr.kind {
                            if matches!(lit.kind, rustc_ast::token::LitKind::Integer) {
                                ne_with_int = true;
                            }
                        }
                        if ne_with_int {
                            let cond = Condition::Bool(BoolCond::new(expr_str, CmpIntKind::Ne));
                            self.cond_map.insert(self.get_source_info(expr.span), cond);
                        } else {
                            let cond = Condition::Bool(BoolCond::new(expr_str, CmpIntKind::No));
                            self.cond_map.insert(self.get_source_info(expr.span), cond);
                        }
                    }
                    _ => {
                        let expr_str = self.get_string_from_span(expr.span);
                        let cond = Condition::Bool(BoolCond::new(expr_str, CmpIntKind::No));
                        self.cond_map.insert(self.get_source_info(expr.span), cond);
                    }
                }
            }
            rustc_ast::ExprKind::Unary(op, subexpr) => {
                // println!("Unary expression found");
                match &op {
                    rustc_ast::UnOp::Not => {
                        // println!("Negation expression found");
                        self.handle_expr(subexpr);
                    }
                    _ => {
                        let expr_str = self.get_string_from_span(expr.span);
                        let cond = Condition::Bool(BoolCond::new(expr_str, CmpIntKind::No));
                        self.cond_map.insert(self.get_source_info(expr.span), cond);
                    }
                }
            }
            rustc_ast::ExprKind::Let(pat, _, _, _) => {
                let expr_str = self.get_string_from_span(expr.span);
                let cond = Condition::Bool(BoolCond::new(expr_str, CmpIntKind::No));
                self.cond_map.insert(self.get_source_info(pat.span), cond);
            }
            rustc_ast::ExprKind::Paren(expr) => {
                self.handle_expr(expr);
            }
            _ => {
                let expr_str = self.get_string_from_span(expr.span);
                let cond = Condition::Bool(BoolCond::new(expr_str, CmpIntKind::No));
                self.cond_map.insert(self.get_source_info(expr.span), cond);
            }
        }
    }

    // fn handle_arms(&self, arms: &ThinVec<rustc_ast::Arm>) {
    //     for arm in arms {
    //         let pat_str = self.get_string_from_span(arm.pat.span);
    //         println!("Pattern: {}", pat_str);
    //         self.handle_pat(&arm.pat);
    //     }
    // }

    fn handle_pat(&mut self, pat: &rustc_ast::Pat) {
        match &pat.kind {
            rustc_ast::PatKind::Or(subpats) => {
                for subpat in subpats {
                    self.handle_pat(subpat);
                }
            }
            rustc_ast::PatKind::Paren(subpat) => {
                self.handle_pat(subpat);
            }
            rustc_ast::PatKind::Struct(_, path, _, _) => {
                let path_str = self.get_string_from_span(path.span);
                println!("Path: {}", path_str);
                self.pat_infos
                    .push((self.get_source_info(path.span), path_str + "{}"));
            }
            rustc_ast::PatKind::TupleStruct(_, path, _) => {
                let path_str = self.get_string_from_span(path.span);
                println!("Path: {}", path_str);
                self.pat_infos
                    .push((self.get_source_info(path.span), path_str + "()"));
            }
            // rustc_ast::PatKind::Lit(expr) => {}
            rustc_ast::PatKind::Wild => {
                println!("Wildcard pattern found");
                self.pat_infos
                    .push((self.get_source_info(pat.span), "_".to_string()));
            }
            _ => {
                let pat_str = self.get_string_from_span(pat.span);
                println!("Pattern: {}", pat_str);
                self.pat_infos
                    .push((self.get_source_info(pat.span), pat_str));
            }
        }
    }

    pub fn print_map(&self) {
        println!("==================Condition Map==================");
        for (source_info, cond) in &self.cond_map {
            println!("Source: {:?}, Condition: {:?}\n", source_info, cond);
        }
        println!("==================Condition Map==================");
    }

    pub fn move_map(self) -> BTreeMap<SourceInfo, Condition> {
        self.cond_map
    }
}

impl<'ast> ASTVisitor<'ast> for ASTBranchVisitor {
    fn visit_expr(&mut self, ex: &'ast rustc_ast::Expr) -> Self::Result {
        match &ex.kind {
            rustc_ast::ExprKind::If(cond_expr, _, _)
            | rustc_ast::ExprKind::While(cond_expr, _, _) => {
                // Do something with the if expression
                // println!("If expression found");
                self.handle_expr(cond_expr);
                // println!("{:#?}", ex);
            }
            rustc_ast::ExprKind::ForLoop { pat, iter, .. } => {
                // Do something with the while expression
                // println!("ForLoop expression found");
                // println!("{:#?}", ex);
                let pat_str = self.get_string_from_span(pat.span);
                // let pat_loc = self.get_source_info(pat.span);
                let iter_str = self.get_string_from_span(iter.span);
                let iter_loc = self.get_source_info(iter.span);
                let cond = Condition::For(ForCond::new(pat_str, iter_str));
                // let source_info = pat_loc.expand(&iter_loc).unwrap();
                // self.cond_map.insert(source_info, cond);
                self.cond_map.insert(iter_loc, cond);
            }
            // rustc_ast::ExprKind::Loop(_, _, _) => {
            //     println!("Loop expression found");
            // }
            rustc_ast::ExprKind::Match(match_expr, arms, _) => {
                // Do something with the match expression
                // println!("Match expression found");
                // println!("{:#?}", ex);
                let match_str = self.get_string_from_span(match_expr.span);
                let mut match_cond = MatchCond::new(match_str);
                // self.handle_arms(arms);
                for arm in arms {
                    self.pat_infos.clear();
                    self.handle_pat(&arm.pat);
                    if let Some(guard) = &arm.guard {
                        self.handle_expr(guard);
                    }
                    let body_source = match &arm.body {
                        Some(body) => Some(self.get_source_info(body.span)),
                        None => None,
                    };
                    for (pat_source, pat) in &self.pat_infos {
                        match_cond.add_arm(pat_source.clone(), pat.clone(), body_source.clone());
                    }
                }
                self.cond_map.insert(
                    self.get_source_info(match_expr.span),
                    Condition::Match(match_cond),
                );
            }
            _ => {}
        }
        visit::walk_expr(self, ex);
    }
}
