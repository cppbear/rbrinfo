use super::condition::{BinKind, BinaryCond, BoolCond, Condition, ForCond, MatchCond, OtherCond};
use super::sourceinfo::SourceInfo;
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

pub struct HIRBranchVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    span_re: Regex,
    source_cond_map: BTreeMap<SourceInfo, Condition>,
}

impl<'tcx> HIRBranchVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let span_re = Regex::new(r"^(.*?):(\d+):(\d+): (\d+):(\d+)").unwrap();
        Self {
            tcx,
            span_re,
            source_cond_map: BTreeMap::new(),
        }
    }

    pub fn print_map(&self) {
        println!("==================Condition Map==================");
        for (source_info, cond) in &self.source_cond_map {
            println!("Source: {:?}, Condition: {:?}", source_info, cond);
        }
        println!("==================Condition Map==================");
    }

    fn handle_binary(
        &mut self,
        op: &Spanned<BinOpKind>,
        expr_source: SourceInfo,
        lexpr: &'tcx rustc_hir::Expr<'tcx>,
        rexpr: &'tcx rustc_hir::Expr<'tcx>,
    ) {
        let lhs = SourceInfo::from_span(lexpr.span, &self.span_re).get_string();
        let rhs = SourceInfo::from_span(rexpr.span, &self.span_re).get_string();
        let mut cmp_with_int = false;
        if let rustc_hir::ExprKind::Lit(lit) = lexpr.kind {
            match lit.node {
                rustc_ast::LitKind::Byte(_)
                | rustc_ast::LitKind::Char(_)
                | rustc_ast::LitKind::Int(_, _)
                | rustc_ast::LitKind::Bool(_) => {
                    cmp_with_int = true;
                }
                _ => {}
            }
        }
        if let rustc_hir::ExprKind::Lit(lit) = rexpr.kind {
            match lit.node {
                rustc_ast::LitKind::Byte(_)
                | rustc_ast::LitKind::Char(_)
                | rustc_ast::LitKind::Int(_, _)
                | rustc_ast::LitKind::Bool(_) => {
                    cmp_with_int = true;
                }
                _ => {}
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
                    expr_source.get_string(),
                    lhs,
                    rhs,
                    cmp_with_int,
                )));
                self.source_cond_map.insert(expr_source, cond);
            }
            rustc_hir::BinOpKind::Ne => {
                let cond = Condition::Bool(BoolCond::Binary(BinaryCond::new(
                    BinKind::Ne,
                    expr_source.get_string(),
                    lhs,
                    rhs,
                    cmp_with_int,
                )));
                self.source_cond_map.insert(expr_source, cond);
            }
            rustc_hir::BinOpKind::Ge => {
                let cond = Condition::Bool(BoolCond::Binary(BinaryCond::new(
                    BinKind::Ge,
                    expr_source.get_string(),
                    lhs,
                    rhs,
                    cmp_with_int,
                )));
                self.source_cond_map.insert(expr_source, cond);
            }
            rustc_hir::BinOpKind::Gt => {
                let cond = Condition::Bool(BoolCond::Binary(BinaryCond::new(
                    BinKind::Gt,
                    expr_source.get_string(),
                    lhs,
                    rhs,
                    cmp_with_int,
                )));
                self.source_cond_map.insert(expr_source, cond);
            }
            rustc_hir::BinOpKind::Le => {
                let cond = Condition::Bool(BoolCond::Binary(BinaryCond::new(
                    BinKind::Le,
                    expr_source.get_string(),
                    lhs,
                    rhs,
                    cmp_with_int,
                )));
                self.source_cond_map.insert(expr_source, cond);
            }
            rustc_hir::BinOpKind::Lt => {
                let cond = Condition::Bool(BoolCond::Binary(BinaryCond::new(
                    BinKind::Lt,
                    expr_source.get_string(),
                    lhs,
                    rhs,
                    cmp_with_int,
                )));
                self.source_cond_map.insert(expr_source, cond);
            }
            _ => {
                let cond = Condition::Bool(BoolCond::Binary(BinaryCond::new(
                    BinKind::Other,
                    expr_source.get_string(),
                    lhs,
                    rhs,
                    false,
                )));
                self.source_cond_map.insert(expr_source, cond);
            }
        }
    }

    fn handle_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
        let expr_source = SourceInfo::from_span(expr.span, &self.span_re);
        let expr_str = expr_source.get_string();
        match &expr.kind {
            rustc_hir::ExprKind::Binary(op, lexpr, rexpr) => {
                self.handle_binary(op, expr_source, lexpr, rexpr);
            }
            rustc_hir::ExprKind::Unary(op, subexpr) => match op {
                rustc_hir::UnOp::Not => {
                    self.handle_expr(subexpr);
                }
                _ => {
                    let cond = Condition::Bool(BoolCond::Other(OtherCond::new(expr_str)));
                    self.source_cond_map.insert(expr_source, cond);
                }
            },
            rustc_hir::ExprKind::Let(let_expr) => {
                let cond = Condition::Bool(BoolCond::Other(OtherCond::new(expr_str)));
                let pat_source = SourceInfo::from_span(let_expr.pat.span, &self.span_re);
                self.source_cond_map.insert(pat_source, cond);
            }
            rustc_hir::ExprKind::DropTemps(temp_expr) => {
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
                let range_source = SourceInfo::from_span(expr.span, &self.span_re);
                let iter_source = SourceInfo::from_span(arms[1].pat.span, &self.span_re);
                let cond_str = format!(
                    "{} in {}",
                    iter_source.get_string(),
                    range_source.get_string()
                );
                let cond = Condition::Bool(BoolCond::Other(OtherCond::new(cond_str)));
                self.source_cond_map.insert(range_source, cond);
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

    // fn handle_

    fn resolve_pat_kind(&self, pat: &'tcx rustc_hir::Pat<'tcx>) -> &'tcx rustc_hir::PatKind<'tcx> {
        match &pat.kind {
            rustc_hir::PatKind::Ref(subpat, _) => {
                return self.resolve_pat_kind(subpat);
            }
            rustc_hir::PatKind::Deref(subpat) => {
                return self.resolve_pat_kind(subpat);
            }
            _ => &pat.kind,
        }
    }

    fn handle_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) {
        let pat_kind = self.resolve_pat_kind(pat);
        match pat_kind {
            rustc_hir::PatKind::Or(subpats) => {
                for subpat in *subpats {
                    self.handle_pat(subpat);
                }
            }
            _ => {}
        }
    }

    fn resolve_match_type(&self, tykind: &'tcx TyKind<'tcx>) -> &'tcx TyKind<'tcx> {
        match tykind {
            TyKind::Ref(_, ty, _) => self.resolve_match_type(ty.kind()),
            _ => tykind,
        }
    }

    fn handle_match(
        &mut self,
        expr: &'tcx rustc_hir::Expr<'tcx>,
        arms: &'tcx [rustc_hir::Arm<'tcx>],
    ) {
        // FIXME: move the adjustment of the match type into the arms
        let match_source = SourceInfo::from_span(expr.span, &self.span_re);
        println!("{:?}, {}", match_source, match_source.get_string());
        let typeck_res = self.tcx.typeck(expr.hir_id.owner);
        let expr_ty = typeck_res.expr_ty(expr);
        println!("Type of {} is {:?}", match_source.get_string(), expr_ty);
        println!("expr_ty.kind() is {:?}", expr_ty.kind());
        let expr_ty = self.resolve_match_type(expr_ty.kind());
        println!("expr_ty is {:?}", expr_ty);
        match expr_ty {
            TyKind::Adt(adt_def, _) => {
                if adt_def.is_enum() {
                    println!("{:?} is enum", expr_ty);
                    let mut iter = 0;
                    for variant in adt_def.variants() {
                        println!("Variant {}: {:?}", iter, variant.name);
                        iter += 1;
                    }
                    iter = 0;
                    for arm in arms {
                        let pat_source = SourceInfo::from_span(arm.pat.span, &self.span_re);
                        println!(
                            "Pattern {}: {:?}, {}",
                            iter,
                            pat_source,
                            pat_source.get_string()
                        );
                        let pat_ty = typeck_res.pat_ty(arm.pat);
                        println!("Type of {} is {:?}", pat_source.get_string(), pat_ty);
                        match arm.pat.kind {
                            rustc_hir::PatKind::Path(qpath)
                            | rustc_hir::PatKind::TupleStruct(qpath, _, _)
                            | rustc_hir::PatKind::Struct(qpath, _, _) => match qpath {
                                rustc_hir::QPath::Resolved(_, path) => {
                                    println!("path.res is: {:?}", path.res);
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
                                            panic!("path.res is: {:?}", path.res);
                                        }
                                    }
                                }
                                _ => {
                                    panic!("qpath is: {:?}", qpath);
                                }
                            },
                            rustc_hir::PatKind::Wild => {}
                            _ => {
                                panic!("arm.pat.kind is: {:?}", arm.pat.kind);
                            }
                        }
                        if let Some(guard) = &arm.guard {
                            self.handle_expr(guard);
                        }
                        iter += 1;
                    }
                }
            }
            TyKind::Tuple(tuple_def) => {}
            _ => {}
        }
        if let TyKind::Adt(adt_def, _) = expr_ty {
            println!("{:?} is Adt", expr_ty);
            if adt_def.is_enum() {
                println!("{:?} is enum", expr_ty);
                let mut iter = 0;
                for variant in adt_def.variants() {
                    println!("Variant {}: {:?}", iter, variant.name);
                    iter += 1;
                }
                iter = 0;
                for arm in arms {
                    let pat_source = SourceInfo::from_span(arm.pat.span, &self.span_re);
                    println!(
                        "Pattern {}: {:?}, {}",
                        iter,
                        pat_source,
                        pat_source.get_string()
                    );
                    let pat_ty = typeck_res.pat_ty(arm.pat);
                    println!("Type of {} is {:?}", pat_source.get_string(), pat_ty);
                    match arm.pat.kind {
                        rustc_hir::PatKind::Path(qpath)
                        | rustc_hir::PatKind::TupleStruct(qpath, _, _)
                        | rustc_hir::PatKind::Struct(qpath, _, _) => match qpath {
                            rustc_hir::QPath::Resolved(_, path) => {
                                println!("path.res is: {:?}", path.res);
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
                                        panic!("path.res is: {:?}", path.res);
                                    }
                                }
                            }
                            _ => {
                                panic!("qpath is: {:?}", qpath);
                            }
                        },
                        rustc_hir::PatKind::Wild => {}
                        _ => {
                            panic!("arm.pat.kind is: {:?}", arm.pat.kind);
                        }
                    }
                    if let Some(guard) = &arm.guard {
                        self.handle_expr(guard);
                    }
                    iter += 1;
                }
            } else if adt_def.is_struct() {
                let mut iter = 0;
                for field in adt_def.all_fields() {
                    println!("Field {}: {:?}", iter, field.name);
                    iter += 1;
                }
                iter = 0;
                for arm in arms {
                    let pat_source = SourceInfo::from_span(arm.pat.span, &self.span_re);
                    println!(
                        "Pattern {}: {:?}, {}",
                        iter,
                        pat_source,
                        pat_source.get_string()
                    );
                    match arm.pat.kind {
                        rustc_hir::PatKind::Struct(_, pat_fields, _) => {
                            for field in pat_fields {
                                let field_name = field.ident.name;
                                let index = adt_def
                                    .all_fields()
                                    .position(|f| f.name == field_name)
                                    .unwrap();
                                println!("Field {}: {:?}", index, field_name);
                                match field.pat.kind {
                                    rustc_hir::PatKind::Lit(lit) => {
                                        if let rustc_hir::ExprKind::Lit(lit) = lit.kind {
                                            match lit.node {
                                                rustc_ast::LitKind::Byte(_)
                                                | rustc_ast::LitKind::Char(_)
                                                | rustc_ast::LitKind::Int(_, _)
                                                | rustc_ast::LitKind::Bool(_) => {
                                                    let lit_str = SourceInfo::from_span(
                                                        lit.span,
                                                        &self.span_re,
                                                    )
                                                    .get_string();
                                                    println!("Literal: {}", lit_str);
                                                }
                                                _ => {}
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }
                        rustc_hir::PatKind::TupleStruct(_, pats, _) => {
                            for pat in pats {
                                match pat.kind {
                                    rustc_hir::PatKind::Lit(lit) => {
                                        if let rustc_hir::ExprKind::Lit(lit) = lit.kind {
                                            match lit.node {
                                                rustc_ast::LitKind::Byte(_)
                                                | rustc_ast::LitKind::Char(_)
                                                | rustc_ast::LitKind::Int(_, _)
                                                | rustc_ast::LitKind::Bool(_) => {
                                                    let lit_str = SourceInfo::from_span(
                                                        lit.span,
                                                        &self.span_re,
                                                    )
                                                    .get_string();
                                                    println!("Literal: {}", lit_str);
                                                }
                                                _ => {}
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }
                        rustc_hir::PatKind::Wild => {}
                        _ => {
                            panic!("arm.pat.kind is: {:?}", arm.pat.kind);
                        }
                    }
                    if let Some(guard) = &arm.guard {
                        self.handle_expr(guard);
                    }
                    iter += 1;
                }
            }
        } else if let TyKind::Tuple(tuple_def) = expr_ty {
            let mut iter = 0;
            for field_ty in *tuple_def {
                println!("Field {}: {:?}", iter, field_ty);
                iter += 1;
            }
            iter = 0;
            for arm in arms {
                let pat_source = SourceInfo::from_span(arm.pat.span, &self.span_re);
                println!(
                    "Pattern {}: {:?}, {}",
                    iter,
                    pat_source,
                    pat_source.get_string()
                );
                match arm.pat.kind {
                    rustc_hir::PatKind::Tuple(pats, _) => {
                        for pat in pats {
                            match pat.kind {
                                rustc_hir::PatKind::Lit(lit) => {
                                    if let rustc_hir::ExprKind::Lit(lit) = lit.kind {
                                        match lit.node {
                                            rustc_ast::LitKind::Byte(_)
                                            | rustc_ast::LitKind::Char(_)
                                            | rustc_ast::LitKind::Int(_, _)
                                            | rustc_ast::LitKind::Bool(_) => {
                                                let lit_str =
                                                    SourceInfo::from_span(lit.span, &self.span_re)
                                                        .get_string();
                                                println!("Literal: {}", lit_str);
                                            }
                                            _ => {}
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    rustc_hir::PatKind::Wild => {}
                    _ => {
                        panic!("arm.pat.kind is: {:?}", arm.pat.kind);
                    }
                }
                if let Some(guard) = &arm.guard {
                    self.handle_expr(guard);
                }
                iter += 1;
            }
        } else if let TyKind::Ref(_, _, _) = expr_ty {
            println!("{:?} is ref", expr_ty);
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
