use super::callback::get_span_string;
use super::condition::{BinKind, BinaryCond, BoolCond, Condition, ForCond, MatchCond, OtherCond};
use regex::Regex;
use rustc_ast::BinOpKind;
use rustc_ast::{
    ptr::P,
    visit::{self, Visitor as ASTVisitor},
};
use rustc_hir::def::DefKind;
use rustc_hir::intravisit::{self, Visitor as HIRVisitor};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::source_map::Spanned;
use std::collections::BTreeMap;
use std::fs::File;
use std::io::{BufRead, BufReader};
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
    pub fn get_string(&self) -> String {
        let file = File::open(&self.file_path).unwrap();
        let reader = BufReader::new(file);

        let mut result = String::new();
        for (line_number, line) in reader.lines().enumerate() {
            let line_number = line_number as i32 + 1; // Convert to 1-based index
            let line = line.unwrap();
            if line_number < self.start_line {
                continue;
            }
            if line_number > self.end_line {
                break;
            }
            let start_col = if line_number == self.start_line {
                (self.start_column - 1) as usize
            } else {
                0
            };
            let end_col = if line_number == self.end_line {
                (self.end_column - 1) as usize
            } else {
                line.len()
            };
            if start_col <= end_col && end_col <= line.len() {
                result.push_str(&line[start_col..end_col]);
            }
            if line_number < self.end_line {
                result.push('\n');
            }
        }
        result
    }

    pub fn substring_source_info(&self, start: usize, length: usize) -> SourceInfo {
        let original = self.get_string();
        let substring = &original[start..start + length];
        let mut current_line = self.start_line;
        let mut current_column = self.start_column;

        // Calculate the starting line and column for the substring
        for (_, c) in original[..start].chars().enumerate() {
            if c == '\n' {
                current_line += 1;
                current_column = 1;
            } else {
                current_column += 1;
            }
        }
        let start_line = current_line;
        let start_column = current_column;
        // Calculate the ending line and column for the substring
        for c in substring.chars() {
            if c == '\n' {
                current_line += 1;
                current_column = 1;
            } else {
                current_column += 1;
            }
        }
        let end_line = current_line;
        let end_column = current_column;
        SourceInfo {
            file_path: self.file_path.clone(),
            start_line,
            start_column,
            end_line,
            end_column,
        }
    }
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
    tcx: TyCtxt<'tcx>,
    span_re: Regex,
}

impl<'tcx> HIRBranchVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let span_re = Regex::new(r"^(.*?):(\d+):(\d+): (\d+):(\d+)").unwrap();
        Self { tcx, span_re }
    }

    fn get_source_info(&self, span: rustc_span::Span) -> SourceInfo {
        let span_str = format!("{:?}", span);
        let caps = self.span_re.captures(&span_str).unwrap();

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

    fn handle_binary(
        &mut self,
        op: &Spanned<BinOpKind>,
        expr_str: String,
        lexpr: &'tcx rustc_hir::Expr<'tcx>,
        rexpr: &'tcx rustc_hir::Expr<'tcx>,
    ) {
        let lhs = self.get_source_info(lexpr.span).get_string();
        let rhs = self.get_source_info(rexpr.span).get_string();
        let mut cmp_with_int = false;
        if let rustc_hir::ExprKind::Lit(lit) = lexpr.kind {
            if matches!(lit.node, rustc_ast::LitKind::Int(_, _)) {
                cmp_with_int = true;
            }
        }
        if let rustc_hir::ExprKind::Lit(lit) = rexpr.kind {
            if matches!(lit.node, rustc_ast::LitKind::Int(_, _)) {
                cmp_with_int = true;
            }
        }
        match op.node {
            rustc_hir::BinOpKind::And | rustc_hir::BinOpKind::Or => {
                self.handle_expr(lexpr);
                self.handle_expr(rexpr);
            }
            rustc_hir::BinOpKind::Eq => {
                let cond = Condition::Bool(BoolCond::Binary(BinaryCond::new(
                    BinKind::Eq,
                    expr_str,
                    lhs,
                    rhs,
                    cmp_with_int,
                )));
                println!("{:?}", cond);
            }
            rustc_hir::BinOpKind::Ne => {
                let cond = Condition::Bool(BoolCond::Binary(BinaryCond::new(
                    BinKind::Ne,
                    expr_str,
                    lhs,
                    rhs,
                    cmp_with_int,
                )));
                println!("{:?}", cond);
            }
            rustc_hir::BinOpKind::Ge => {
                let cond = Condition::Bool(BoolCond::Binary(BinaryCond::new(
                    BinKind::Ge,
                    expr_str,
                    lhs,
                    rhs,
                    cmp_with_int,
                )));
                println!("{:?}", cond);
            }
            rustc_hir::BinOpKind::Gt => {
                let cond = Condition::Bool(BoolCond::Binary(BinaryCond::new(
                    BinKind::Gt,
                    expr_str,
                    lhs,
                    rhs,
                    cmp_with_int,
                )));
                println!("{:?}", cond);
            }
            rustc_hir::BinOpKind::Le => {
                let cond = Condition::Bool(BoolCond::Binary(BinaryCond::new(
                    BinKind::Le,
                    expr_str,
                    lhs,
                    rhs,
                    cmp_with_int,
                )));
                println!("{:?}", cond);
            }
            rustc_hir::BinOpKind::Lt => {
                let cond = Condition::Bool(BoolCond::Binary(BinaryCond::new(
                    BinKind::Lt,
                    expr_str,
                    lhs,
                    rhs,
                    cmp_with_int,
                )));
                println!("{:?}", cond);
            }
            _ => {
                let cond = Condition::Bool(BoolCond::Binary(BinaryCond::new(
                    BinKind::Other,
                    expr_str,
                    lhs,
                    rhs,
                    false,
                )));
                println!("{:?}", cond);
            }
        }
    }

    fn handle_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
        let expr_str = self.get_source_info(expr.span).get_string();
        match &expr.kind {
            rustc_hir::ExprKind::Binary(op, lexpr, rexpr) => {
                // println!("Binary expression found");
                self.handle_binary(op, expr_str, lexpr, rexpr);
            }
            rustc_hir::ExprKind::Unary(op, subexpr) => {
                // println!("Unary expression found");
                match op {
                    rustc_hir::UnOp::Not => {
                        // println!("Negation expression found");
                        self.handle_expr(subexpr);
                    }
                    _ => {
                        let cond = Condition::Bool(BoolCond::Other(OtherCond::new(expr_str)));
                        println!("{:?}", cond);
                    }
                }
            }
            rustc_hir::ExprKind::Let(let_expr) => {
                // println!("Let expression found");
                let cond = Condition::Bool(BoolCond::Other(OtherCond::new(expr_str)));
                println!("{:?}", cond);
            }
            rustc_hir::ExprKind::DropTemps(temp_expr) => {
                // println!("DropTemps expression found");
                self.handle_expr(temp_expr);
            }
            _ => {}
        }
    }

    fn handle_forloop(&mut self, block: &rustc_hir::Block) {
        let stmt = block.stmts[0];
        if let rustc_hir::StmtKind::Expr(expr) = stmt.kind {
            if let rustc_hir::ExprKind::Match(_, arms, match_kind) = expr.kind {
                assert_eq!(match_kind, rustc_hir::MatchSource::ForLoopDesugar);
                let range_source = self.get_source_info(expr.span);
                let iter_source = self.get_source_info(arms[1].pat.span);
                let cond_str = format!(
                    "{} in {}",
                    iter_source.get_string(),
                    range_source.get_string()
                );
                let cond = Condition::Bool(BoolCond::Other(OtherCond::new(cond_str)));
                println!("{:?}", cond);
            } else {
                panic!(
                    "The ExprKind of the first stmt in ForLoop is {:?}.",
                    expr.kind
                );
            }
        } else {
            panic!(
                "The StmtKind of the first stmt in ForLoop is {:?}.",
                stmt.kind
            );
        }
    }

    fn handle_match(
        &mut self,
        expr: &'tcx rustc_hir::Expr<'tcx>,
        arms: &'tcx [rustc_hir::Arm<'tcx>],
    ) {
        let match_source = self.get_source_info(expr.span);
        println!("{:?}, {}", match_source, match_source.get_string());
        let typeck_res = self.tcx.typeck(expr.hir_id.owner);
        let expr_ty = typeck_res.expr_ty(expr);
        println!("Type of {} is {:?}", match_source.get_string(), expr_ty);
        if let TyKind::Adt(adt_def, _) = expr_ty.kind() {
            if adt_def.is_enum() {
                let mut iter = 0;
                for variant in adt_def.variants() {
                    println!("Variant {}: {:?}", iter, variant.name);
                    iter += 1;
                }
                let mut iter = 0;
                for arm in arms {
                    let pat_source = self.get_source_info(arm.pat.span);
                    println!(
                        "Pattern {}: {:?}, {}",
                        iter,
                        pat_source,
                        pat_source.get_string()
                    );
                    if let rustc_hir::PatKind::Path(qpath)
                    | rustc_hir::PatKind::TupleStruct(qpath, _, _)
                    | rustc_hir::PatKind::Struct(qpath, _, _) = arm.pat.kind
                    {
                        if let rustc_hir::QPath::Resolved(_, path) = qpath {
                            println!("{:?}", path.res);
                            match path.res {
                                rustc_hir::def::Res::Def(
                                    rustc_hir::def::DefKind::Ctor(
                                        rustc_hir::def::CtorOf::Variant,
                                        _,
                                    ),
                                    ctor_def_id,
                                ) => {
                                    let variant_index =
                                        adt_def.variant_index_with_ctor_id(ctor_def_id);
                                    println!("variant_index: {}", variant_index.index());
                                }
                                rustc_hir::def::Res::Def(
                                    rustc_hir::def::DefKind::Variant,
                                    variant_def_id,
                                ) => {
                                    let variant_index =
                                        adt_def.variant_index_with_id(variant_def_id);
                                    println!("variant_index: {}", variant_index.index());
                                }
                                _ => {
                                    panic!("{:?}", path.res);
                                }
                            }
                        } else {
                            panic!("{:?}", qpath);
                        }
                    } else {
                        panic!("{:?}", arm.pat.kind);
                    }
                    // TODO: handle guard

                    iter += 1;
                }
            } else if adt_def.is_struct() {
                // TODO: handle struct
                let mut iter = 0;
                for field in adt_def.all_fields() {
                    println!("Field {}: {:?}", iter, field.name);
                    iter += 1;
                }
            }
        } else if let TyKind::Tuple(tuple_def) = expr_ty.kind() {
            // TODO: handle tuple
            let mut iter = 0;
            for field_ty in *tuple_def {
                println!("Field {}: {:?}", iter, field_ty);
                iter += 1;
            }
        }
    }
}

impl<'tcx> HIRVisitor<'tcx> for HIRBranchVisitor<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx rustc_hir::Expr<'tcx>) -> Self::Result {
        match &ex.kind {
            rustc_hir::ExprKind::If(cond_expr, _, _) => {
                self.handle_expr(cond_expr);
            }
            rustc_hir::ExprKind::Loop(block, _, loop_kind, _) => {
                if let rustc_hir::LoopSource::ForLoop = loop_kind {
                    self.handle_forloop(block);
                }
            }
            rustc_hir::ExprKind::Match(expr, arms, match_kind) => {
                // Do something with the match expression
                // println!("Match expression found");
                // println!("{:#?}", ex);
                /*
                println!("{:?}", self.tcx.hir().node_to_string(expr.hir_id));
                println!("{:?}", self.tcx.type_of(expr.hir_id.owner.to_def_id()));
                let local_def_id = self.tcx.hir().enclosing_body_owner(expr.hir_id);
                let typeck_res = self
                    .tcx
                    .typeck_body(self.tcx.hir().body_owned_by(local_def_id).id());
                let expr_ty = typeck_res.expr_ty(expr);
                println!("{:?}", expr_ty);
                if let TyKind::Adt(adt_def, _) = expr_ty.kind() {
                    if adt_def.is_enum() {
                        let mut num = 0;
                        for variant in adt_def.variants() {
                            println!("Variant {}: {:?}", num, variant.name);
                            num += 1;
                            for field in variant.fields.iter() {
                                let field_ty = self.tcx.type_of(field.did);
                                println!("Field: {:?}, Type: {:?}", field.name, field_ty);
                            }
                        }
                    }
                }
                */
                if let rustc_hir::MatchSource::Normal = match_kind {
                    self.handle_match(expr, arms);
                }
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

/*
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
 */
