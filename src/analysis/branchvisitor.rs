use super::condition::{
    Arm, BinKind, BinaryCond, BoolCond, Condition, ForCond, MatchCond, Patt, PattKind,
};
use super::sourceinfo::SourceInfo;
use regex::Regex;
use rustc_ast::BinOpKind;
use rustc_hir::intravisit::{self, Visitor as HIRVisitor};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::source_map::Spanned;
use std::collections::HashMap;

pub struct HIRBranchVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    span_re: Regex,
    typeck_res: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
    source_cond_map: HashMap<SourceInfo, Condition>,
}

impl<'tcx> HIRBranchVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, typeck_res: &'tcx rustc_middle::ty::TypeckResults<'tcx>) -> Self {
        let span_re = Regex::new(r"^(.*?):(\d+):(\d+): (\d+):(\d+)").unwrap();
        Self {
            tcx,
            span_re,
            typeck_res,
            source_cond_map: HashMap::new(),
        }
    }

    pub fn print_map(&self) {
        println!("==================Condition Map==================");
        for (source_info, cond) in &self.source_cond_map {
            println!("Source: {:?}\nCondition: {:#?}\n", source_info, cond);
        }
        println!("==================Condition Map==================");
    }

    fn is_comparable_literal(expr: &rustc_hir::Expr) -> bool {
        if let rustc_hir::ExprKind::Lit(lit) = expr.kind {
            matches!(
                lit.node,
                rustc_ast::LitKind::Byte(_)
                    | rustc_ast::LitKind::Char(_)
                    | rustc_ast::LitKind::Int(_, _)
            )
        } else {
            false
        }
    }

    fn handle_binary(
        &self,
        op: &Spanned<BinOpKind>,
        expr_source: SourceInfo,
        lexpr: &'tcx rustc_hir::Expr<'tcx>,
        rexpr: &'tcx rustc_hir::Expr<'tcx>,
    ) -> HashMap<SourceInfo, Condition> {
        let lhs = SourceInfo::from_span(lexpr.span, &self.span_re).get_string();
        let rhs = SourceInfo::from_span(rexpr.span, &self.span_re).get_string();
        let cmp_with_int = Self::is_comparable_literal(lexpr) || Self::is_comparable_literal(rexpr);
        let mut map = HashMap::new();
        match op.node {
            rustc_hir::BinOpKind::And | rustc_hir::BinOpKind::Or => {
                map.extend(self.handle_expr(lexpr));
                map.extend(self.handle_expr(rexpr));
            }
            _ => {
                let kind = match op.node {
                    BinOpKind::Eq => BinKind::Eq,
                    BinOpKind::Ne => BinKind::Ne,
                    BinOpKind::Ge => BinKind::Ge,
                    BinOpKind::Gt => BinKind::Gt,
                    BinOpKind::Le => BinKind::Le,
                    BinOpKind::Lt => BinKind::Lt,
                    _ => BinKind::Other,
                };
                let cond = Condition::Bool(BoolCond::Binary(BinaryCond {
                    kind,
                    expr: expr_source.get_string(),
                    lhs,
                    rhs,
                    cmp_with_int,
                }));
                map.insert(expr_source, cond);
            }
        }
        map
    }

    fn handle_expr(&self, expr: &'tcx rustc_hir::Expr<'tcx>) -> HashMap<SourceInfo, Condition> {
        let expr_source = SourceInfo::from_span(expr.span, &self.span_re);
        let expr_str = expr_source.get_string();
        let mut map = HashMap::new();
        match &expr.kind {
            rustc_hir::ExprKind::Binary(op, lexpr, rexpr) => {
                map.extend(self.handle_binary(op, expr_source, lexpr, rexpr));
            }
            rustc_hir::ExprKind::Unary(op, subexpr) => match op {
                rustc_hir::UnOp::Not => {
                    map.extend(self.handle_expr(subexpr));
                }
                _ => {
                    let cond = Condition::Bool(BoolCond::Other(expr_str));
                    map.insert(expr_source, cond);
                }
            },
            rustc_hir::ExprKind::Let(let_expr) => {
                let cond = Condition::Bool(BoolCond::Other(expr_str));
                let pat_source = SourceInfo::from_span(let_expr.pat.span, &self.span_re);
                map.insert(pat_source, cond);
            }
            rustc_hir::ExprKind::DropTemps(temp_expr) => {
                map.extend(self.handle_expr(temp_expr));
            }
            _ => {
                panic!("Unsupported expression kind: {:?}", expr.kind);
            }
        }
        map
    }

    fn handle_forloop(&mut self, block: &rustc_hir::Block) {
        let stmt = block.stmts[0];
        if let rustc_hir::StmtKind::Expr(expr) = stmt.kind {
            if let rustc_hir::ExprKind::Match(_, arms, match_kind) = expr.kind {
                assert_eq!(match_kind, rustc_hir::MatchSource::ForLoopDesugar);
                let var_source = SourceInfo::from_span(arms[1].pat.span, &self.span_re);
                let range_source = SourceInfo::from_span(expr.span, &self.span_re);
                let cond = Condition::For(ForCond {
                    iter_var: var_source.get_string(),
                    iter_range: range_source.get_string(),
                });
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

    fn resolve_pat_kind(&self, pat: &'tcx rustc_hir::Pat<'tcx>) -> rustc_hir::PatKind<'tcx> {
        match pat.kind {
            rustc_hir::PatKind::Ref(subpat, _) | rustc_hir::PatKind::Deref(subpat) => {
                return self.resolve_pat_kind(subpat);
            }
            _ => pat.kind,
        }
    }

    fn handle_enum_pat(
        &self,
        pat: &'tcx rustc_hir::Pat<'tcx>,
        adt_def: &'tcx rustc_middle::ty::AdtDef<'tcx>,
    ) -> HashMap<SourceInfo, Patt> {
        let mut map = HashMap::new();
        let pat_source = SourceInfo::from_span(pat.span, &self.span_re);
        // println!("Pattern: {:?}, {}", pat_source, pat_source.get_string());
        // let pat_ty = self.typeck_res.pat_ty(pat);
        // println!("Type of {} is {:?}", pat_source.get_string(), pat_ty);
        let pat_kind = self.resolve_pat_kind(pat);
        match pat_kind {
            rustc_hir::PatKind::Path(qpath)
            | rustc_hir::PatKind::TupleStruct(qpath, _, _)
            | rustc_hir::PatKind::Struct(qpath, _, _) => match qpath {
                rustc_hir::QPath::Resolved(_, path) => {
                    // println!("path.res is: {:?}", path.res);
                    match path.res {
                        rustc_hir::def::Res::Def(
                            rustc_hir::def::DefKind::Ctor(rustc_hir::def::CtorOf::Variant, _),
                            ctor_def_id,
                        ) => {
                            let variant_index = adt_def.variant_index_with_ctor_id(ctor_def_id);
                            // println!("variant_index: {}", variant_index.index());
                            let patt = Patt {
                                pat_str: pat_source.get_string(),
                                kind: PattKind::Enum(variant_index.index()),
                            };
                            map.insert(pat_source, patt);
                        }
                        rustc_hir::def::Res::Def(
                            rustc_hir::def::DefKind::Variant,
                            variant_def_id,
                        ) => {
                            let variant_index = adt_def.variant_index_with_id(variant_def_id);
                            // println!("variant_index: {}", variant_index.index());
                            let patt = Patt {
                                pat_str: pat_source.get_string(),
                                kind: PattKind::Enum(variant_index.index()),
                            };
                            map.insert(pat_source, patt);
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
            _ => {
                panic!("pat_kind is: {:?}", pat.kind);
            }
        }
        map
    }

    fn handle_struct_pat(
        &self,
        pat: &'tcx rustc_hir::Pat<'tcx>,
        adt_def: &'tcx rustc_middle::ty::AdtDef<'tcx>,
    ) -> HashMap<SourceInfo, Patt> {
        let mut map = HashMap::new();
        let pat_source = SourceInfo::from_span(pat.span, &self.span_re);
        // println!("Pattern: {:?}, {}", pat_source, pat_source.get_string());
        let pat_kind = self.resolve_pat_kind(pat);
        match pat_kind {
            rustc_hir::PatKind::Struct(_, fields, _) => {
                let mut patt = Patt {
                    pat_str: pat_source.get_string(),
                    kind: PattKind::StructOrTuple(HashMap::new()),
                };
                for field in fields {
                    let field_name = field.ident.name;
                    let index = adt_def
                        .all_fields()
                        .position(|f| f.name == field_name)
                        .unwrap();
                    // println!("Field {}: {:?}", index, field_name);
                    let field_pat_kind = self.resolve_pat_kind(&field.pat);
                    match field_pat_kind {
                        rustc_hir::PatKind::Lit(lit) => match lit.kind {
                            rustc_hir::ExprKind::Lit(lit) => match lit.node {
                                rustc_ast::LitKind::Byte(_)
                                | rustc_ast::LitKind::Char(_)
                                | rustc_ast::LitKind::Int(_, _) => {
                                    let lit_str =
                                        SourceInfo::from_span(lit.span, &self.span_re).get_string();
                                    println!("Literal: {}", lit_str);
                                }
                                _ => {}
                            },
                            rustc_hir::ExprKind::Unary(op, expr) => {
                                assert_eq!(op, rustc_hir::UnOp::Neg);
                                if let rustc_hir::ExprKind::Lit(lit) = expr.kind {
                                    match lit.node {
                                        rustc_ast::LitKind::Int(_, _) => {
                                            let lit_str =
                                                SourceInfo::from_span(lit.span, &self.span_re)
                                                    .get_string();
                                            println!("Literal: {}", lit_str);
                                        }
                                        _ => {}
                                    }
                                } else {
                                    panic!("expr.kind is: {:?}", expr.kind);
                                }
                            }
                            _ => {}
                        },
                        _ => {}
                    }
                }
            }
            rustc_hir::PatKind::TupleStruct(_, fields, _) => {
                for field in fields {
                    let field_pat_kind = self.resolve_pat_kind(field);
                    match field_pat_kind {
                        rustc_hir::PatKind::Lit(lit) => match lit.kind {
                            rustc_hir::ExprKind::Lit(lit) => match lit.node {
                                rustc_ast::LitKind::Byte(_)
                                | rustc_ast::LitKind::Char(_)
                                | rustc_ast::LitKind::Int(_, _) => {
                                    let lit_str =
                                        SourceInfo::from_span(lit.span, &self.span_re).get_string();
                                    println!("Literal: {}", lit_str);
                                }
                                _ => {}
                            },
                            rustc_hir::ExprKind::Unary(op, expr) => {
                                assert_eq!(op, rustc_hir::UnOp::Neg);
                                if let rustc_hir::ExprKind::Lit(lit) = expr.kind {
                                    match lit.node {
                                        rustc_ast::LitKind::Int(_, _) => {
                                            let lit_str =
                                                SourceInfo::from_span(lit.span, &self.span_re)
                                                    .get_string();
                                            println!("Literal: {}", lit_str);
                                        }
                                        _ => {}
                                    }
                                } else {
                                    panic!("expr.kind is: {:?}", expr.kind);
                                }
                            }
                            _ => {}
                        },
                        _ => {}
                    }
                }
            }
            _ => {
                panic!("pat_kind is: {:?}", pat_kind);
            }
        }
        map
    }

    fn handle_adt_pat(
        &self,
        pat: &'tcx rustc_hir::Pat<'tcx>,
        adt_def: &'tcx rustc_middle::ty::AdtDef<'tcx>,
    ) -> HashMap<SourceInfo, Patt> {
        let mut map = HashMap::new();
        let pat_source = SourceInfo::from_span(pat.span, &self.span_re);
        println!("Pattern: {:?}, {}", pat_source, pat_source.get_string());
        // let pat_ty = self.typeck_res.pat_ty(pat);
        // println!("Type of {} is {:?}", pat_source.get_string(), pat_ty);
        let pat_kind = self.resolve_pat_kind(pat);
        // println!("pat_kind is: {:?}", pat_kind);
        match pat_kind {
            rustc_hir::PatKind::Or(subpats) => {
                for subpat in subpats {
                    map.extend(self.handle_adt_pat(subpat, adt_def));
                }
            }
            rustc_hir::PatKind::Wild => {}
            _ => {
                if adt_def.is_enum() {
                    map.extend(self.handle_enum_pat(pat, adt_def));
                } else if adt_def.is_struct() {
                    map.extend(self.handle_struct_pat(pat, adt_def));
                }
            }
        }
        map
    }

    fn handle_tuple_pat(
        &self,
        pat: &'tcx rustc_hir::Pat<'tcx>,
        tuple_def: &'tcx [rustc_middle::ty::Ty<'tcx>],
    ) -> HashMap<SourceInfo, Patt> {
        let mut map = HashMap::new();
        let pat_source = SourceInfo::from_span(pat.span, &self.span_re);
        println!("Pattern: {:?}, {}", pat_source, pat_source.get_string());
        let pat_kind = self.resolve_pat_kind(pat);
        match pat_kind {
            rustc_hir::PatKind::Or(subpats) => {
                for subpat in subpats {
                    map.extend(self.handle_tuple_pat(subpat, tuple_def));
                }
            }
            rustc_hir::PatKind::Tuple(fields, pos) => {
                // TODO: get the index of each pattern in the tuple
                for field in fields {
                    let field_pat_kind = self.resolve_pat_kind(field);
                    match field_pat_kind {
                        rustc_hir::PatKind::Lit(lit) => match lit.kind {
                            rustc_hir::ExprKind::Lit(lit) => match lit.node {
                                rustc_ast::LitKind::Byte(_)
                                | rustc_ast::LitKind::Char(_)
                                | rustc_ast::LitKind::Int(_, _) => {
                                    let lit_str =
                                        SourceInfo::from_span(lit.span, &self.span_re).get_string();
                                    println!("Literal: {}", lit_str);
                                }
                                _ => {}
                            },
                            rustc_hir::ExprKind::Unary(op, expr) => {
                                assert_eq!(op, rustc_hir::UnOp::Neg);
                                if let rustc_hir::ExprKind::Lit(lit) = expr.kind {
                                    match lit.node {
                                        rustc_ast::LitKind::Int(_, _) => {
                                            let lit_str =
                                                SourceInfo::from_span(lit.span, &self.span_re)
                                                    .get_string();
                                            println!("Literal: {}", lit_str);
                                        }
                                        _ => {}
                                    }
                                } else {
                                    panic!("expr.kind is: {:?}", expr.kind);
                                }
                            }
                            _ => {}
                        },
                        _ => {}
                    }
                }
            }
            rustc_hir::PatKind::Wild => {}
            _ => {
                panic!("pat.kind is: {:?}", pat.kind);
            }
        }
        map
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
        let match_source = SourceInfo::from_span(expr.span, &self.span_re);
        let mut cond = MatchCond::new(match_source.get_string());
        let expr_ty = self.typeck_res.expr_ty(expr);
        let expr_ty = self.resolve_match_type(expr_ty.kind());

        match expr_ty {
            TyKind::Adt(adt_def, _) => {
                for arm in arms {
                    let patt_map = self.handle_adt_pat(arm.pat, adt_def);
                    let mut guard_map = None;
                    if let Some(guard) = arm.guard {
                        guard_map = Some(self.handle_expr(guard));
                    }
                    let body_source = SourceInfo::from_span(arm.body.span, &self.span_re);
                    for (source_info, patt) in patt_map {
                        let arm = Arm {
                            pat: patt.clone(),
                            guard: guard_map.clone(),
                            body_source: body_source.clone(),
                        };
                        cond.arms.insert(source_info, arm);
                    }
                    // cond.arms.extend(arm_map);
                }
            }
            TyKind::Tuple(tuple_def) => {
                for arm in arms {
                    let patt_map = self.handle_tuple_pat(arm.pat, tuple_def);
                    let mut guard_map = None;
                    if let Some(guard) = &arm.guard {
                        guard_map = Some(self.handle_expr(guard));
                    }
                    let body_source = SourceInfo::from_span(arm.body.span, &self.span_re);
                    for (source_info, patt) in patt_map {
                        let arm = Arm {
                            pat: patt.clone(),
                            guard: guard_map.clone(),
                            body_source: body_source.clone(),
                        };
                        cond.arms.insert(source_info, arm);
                    }
                }
            }
            _ => {
                // TODO: handle other types of match expressions
            }
        }
        self.source_cond_map
            .insert(match_source, Condition::Match(cond));
    }
}

impl<'tcx> HIRVisitor<'tcx> for HIRBranchVisitor<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx rustc_hir::Expr<'tcx>) -> Self::Result {
        match &ex.kind {
            rustc_hir::ExprKind::If(cond_expr, _, _) => {
                self.source_cond_map.extend(self.handle_expr(cond_expr));
            }
            rustc_hir::ExprKind::Loop(block, _, loop_kind, _) => {
                if let rustc_hir::LoopSource::ForLoop = loop_kind {
                    self.handle_forloop(block);
                }
            }
            rustc_hir::ExprKind::Match(expr, arms, match_kind) => {
                if let rustc_hir::MatchSource::Normal = match_kind {
                    self.handle_match(expr, arms)
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, ex);
    }
}

pub struct ASTBranchVisitor {
    re: Regex,
    cond_map: HashMap<SourceInfo, Condition>,
    // pat_infos: Vec<(SourceInfo, String)>,
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
