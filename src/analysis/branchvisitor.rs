use super::condition::{
    Arm, BinKind, BinaryCond, BoolCond, Condition, ForCond, MatchCond, Patt, PattKind,
};
use super::sourceinfo::SourceInfo;
use regex::Regex;
use rustc_ast::BinOpKind;
use rustc_hir::intravisit::{self, Visitor as HIRVisitor};
use rustc_middle::ty::{self, TyCtxt, TyKind};
use rustc_span::source_map::Spanned;
use std::collections::HashMap;
use std::fs::{self, File};
use std::io::Write;

pub struct BranchVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    span_re: Regex,
    typeck_res: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
    source_cond_map: HashMap<SourceInfo, Condition>,
}

impl<'tcx> BranchVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, typeck_res: &'tcx rustc_middle::ty::TypeckResults<'tcx>) -> Self {
        let span_re = Regex::new(r"^(.*?):(\d+):(\d+): (\d+):(\d+)").unwrap();
        Self {
            tcx,
            span_re,
            typeck_res,
            source_cond_map: HashMap::new(),
        }
    }

    pub fn output_map(&self) {
        let map_str = &format!("{:#?}\n", self.source_cond_map);
        let dir_path = "./cond_map";
        let file_path = format!("{}/map.txt", dir_path);
        fs::create_dir_all(dir_path).unwrap();
        let mut file = File::create(file_path).unwrap();
        file.write_all(map_str.as_bytes()).unwrap();
    }

    pub fn move_map(self) -> HashMap<SourceInfo, Condition> {
        self.source_cond_map
    }

    fn is_comparable_literal(expr: &rustc_hir::Expr) -> bool {
        match expr.kind {
            rustc_hir::ExprKind::Lit(lit) => {
                matches!(
                    lit.node,
                    rustc_ast::LitKind::Byte(_)
                        | rustc_ast::LitKind::Char(_)
                        | rustc_ast::LitKind::Int(_, _)
                )
            }
            rustc_hir::ExprKind::Unary(op, subexpr) => {
                matches!(op, rustc_hir::UnOp::Neg)
                    && match subexpr.kind {
                        rustc_hir::ExprKind::Lit(lit) => {
                            matches!(
                                lit.node,
                                rustc_ast::LitKind::Byte(_)
                                    | rustc_ast::LitKind::Char(_)
                                    | rustc_ast::LitKind::Int(_, _)
                            )
                        }
                        _ => false,
                    }
            }
            _ => false,
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
    ) -> (SourceInfo, Patt) {
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
                            (pat_source, patt)
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
                            (pat_source, patt)
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
    }

    fn lit_to_constant(
        &self,
        lit_kind: &rustc_ast::LitKind,
        width: rustc_abi::Size,
        neg: bool,
    ) -> u128 {
        match lit_kind {
            rustc_ast::LitKind::Byte(b) => *b as u128,
            rustc_ast::LitKind::Char(ch) => *ch as u128,
            rustc_ast::LitKind::Int(n, _) => width.truncate(if neg {
                (n.get() as i128).overflowing_neg().0 as u128
            } else {
                n.get()
            }),
            _ => {
                panic!("lit_kind is: {:?}", lit_kind);
            }
        }
    }

    fn handle_struct_pat(
        &self,
        pat: &'tcx rustc_hir::Pat<'tcx>,
        adt_def: &'tcx rustc_middle::ty::AdtDef<'tcx>,
    ) -> (SourceInfo, Patt) {
        let pat_source = SourceInfo::from_span(pat.span, &self.span_re);
        // println!("Pattern: {:?}, {}", pat_source, pat_source.get_string());
        let pat_kind = self.resolve_pat_kind(pat);
        match pat_kind {
            rustc_hir::PatKind::Struct(_, fields, _) => {
                let mut lit_map = HashMap::new();
                for field in fields {
                    let field_name = field.ident.name;
                    let index = adt_def
                        .all_fields()
                        .position(|f| f.name == field_name)
                        .unwrap();
                    // println!("Field {}: {:?}", index, field_name);
                    let field_pat_kind = self.resolve_pat_kind(&field.pat);
                    let mut mir_const = None;
                    match field_pat_kind {
                        rustc_hir::PatKind::Lit(pat_lit) => match pat_lit.kind {
                            rustc_hir::ExprKind::Lit(expr_lit) => match expr_lit.node {
                                rustc_ast::LitKind::Byte(_)
                                | rustc_ast::LitKind::Char(_)
                                | rustc_ast::LitKind::Int(_, _) => {
                                    // let lit_str =
                                    //     SourceInfo::from_span(expr_lit.span, &self.span_re)
                                    //         .get_string();
                                    let lit_ty = self.typeck_res.node_type(pat_lit.hir_id);
                                    let param_ty = ty::ParamEnv::reveal_all().and(lit_ty);
                                    let width = self.tcx.layout_of(param_ty).unwrap().size;
                                    // println!("Field type layout: {:?}", layout);
                                    mir_const =
                                        Some(self.lit_to_constant(&expr_lit.node, width, false));
                                    // println!("Literal: {}, mir_const: {:?}", lit_str, mir_const);
                                }
                                _ => {}
                            },
                            rustc_hir::ExprKind::Unary(op, expr) => {
                                assert_eq!(op, rustc_hir::UnOp::Neg);
                                if let rustc_hir::ExprKind::Lit(expr_lit) = expr.kind {
                                    match expr_lit.node {
                                        rustc_ast::LitKind::Int(_, _) => {
                                            // let lit_str =
                                            //     SourceInfo::from_span(expr_lit.span, &self.span_re)
                                            //         .get_string();
                                            let lit_ty = self.typeck_res.node_type(pat_lit.hir_id);
                                            let param_ty = ty::ParamEnv::reveal_all().and(lit_ty);
                                            let width = self.tcx.layout_of(param_ty).unwrap().size;
                                            // println!("Field type layout: {:?}", layout);
                                            mir_const = Some(self.lit_to_constant(
                                                &expr_lit.node,
                                                width,
                                                true,
                                            ));
                                            // println!(
                                            //     "Literal: -{}, mir_const: {:?}",
                                            //     lit_str, mir_const
                                            // );
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
                    lit_map.insert(index, mir_const);
                }
                let patt = Patt {
                    pat_str: pat_source.get_string(),
                    kind: PattKind::StructLike(lit_map),
                };
                (pat_source, patt)
            }
            rustc_hir::PatKind::TupleStruct(_, fields, pos) => {
                let offset = adt_def.all_fields().count() - fields.len();
                let mut lit_map = HashMap::new();
                let mut index = 0;
                for field in fields {
                    if pos.as_opt_usize().map_or(false, |dot_pos| index == dot_pos) {
                        index += offset;
                    }
                    let field_pat_kind = self.resolve_pat_kind(field);
                    let mut mir_const = None;
                    match field_pat_kind {
                        rustc_hir::PatKind::Lit(pat_lit) => match pat_lit.kind {
                            rustc_hir::ExprKind::Lit(expr_lit) => match expr_lit.node {
                                rustc_ast::LitKind::Byte(_)
                                | rustc_ast::LitKind::Char(_)
                                | rustc_ast::LitKind::Int(_, _) => {
                                    // let lit_str =
                                    //     SourceInfo::from_span(expr_lit.span, &self.span_re)
                                    //         .get_string();
                                    let lit_ty = self.typeck_res.node_type(pat_lit.hir_id);
                                    let param_ty = ty::ParamEnv::reveal_all().and(lit_ty);
                                    let width = self.tcx.layout_of(param_ty).unwrap().size;
                                    // println!("Field type layout: {:?}", layout);
                                    mir_const =
                                        Some(self.lit_to_constant(&expr_lit.node, width, false));
                                    // println!("Literal: {}, mir_const: {:?}", lit_str, mir_const);
                                }
                                _ => {}
                            },
                            rustc_hir::ExprKind::Unary(op, expr) => {
                                assert_eq!(op, rustc_hir::UnOp::Neg);
                                if let rustc_hir::ExprKind::Lit(expr_lit) = expr.kind {
                                    match expr_lit.node {
                                        rustc_ast::LitKind::Int(_, _) => {
                                            // let lit_str =
                                            //     SourceInfo::from_span(expr_lit.span, &self.span_re)
                                            //         .get_string();
                                            let lit_ty = self.typeck_res.node_type(pat_lit.hir_id);
                                            let param_ty = ty::ParamEnv::reveal_all().and(lit_ty);
                                            let width = self.tcx.layout_of(param_ty).unwrap().size;
                                            // println!("Field type layout: {:?}", layout);
                                            mir_const = Some(self.lit_to_constant(
                                                &expr_lit.node,
                                                width,
                                                true,
                                            ));
                                            // println!(
                                            //     "Literal: -{}, mir_const: {:?}",
                                            //     lit_str, mir_const
                                            // );
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
                    lit_map.insert(index, mir_const);
                    index += 1;
                }
                let patt = Patt {
                    pat_str: pat_source.get_string(),
                    kind: PattKind::StructLike(lit_map),
                };
                (pat_source, patt)
            }
            _ => {
                panic!("pat_kind is: {:?}", pat_kind);
            }
        }
    }

    fn handle_adt_pat(
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
        // println!("pat_kind is: {:?}", pat_kind);
        match pat_kind {
            rustc_hir::PatKind::Or(subpats) => {
                for subpat in subpats {
                    map.extend(self.handle_adt_pat(subpat, adt_def));
                }
            }
            rustc_hir::PatKind::Wild => {
                let patt = Patt {
                    pat_str: pat_source.get_string(),
                    kind: PattKind::Wild,
                };
                map.insert(pat_source, patt);
            }
            _ => {
                if adt_def.is_enum() {
                    let (pat_source, patt) = self.handle_enum_pat(pat, adt_def);
                    map.insert(pat_source, patt);
                } else if adt_def.is_struct() {
                    let (pat_source, patt) = self.handle_struct_pat(pat, adt_def);
                    map.insert(pat_source, patt);
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
        // println!("Pattern: {:?}, {}", pat_source, pat_source.get_string());
        let pat_kind = self.resolve_pat_kind(pat);
        match pat_kind {
            rustc_hir::PatKind::Or(subpats) => {
                for subpat in subpats {
                    map.extend(self.handle_tuple_pat(subpat, tuple_def));
                }
            }
            rustc_hir::PatKind::Tuple(fields, pos) => {
                let offset = tuple_def.len() - fields.len();
                let mut lit_map = HashMap::new();
                let mut index = 0;
                for field in fields {
                    if pos.as_opt_usize().map_or(false, |dot_pos| index == dot_pos) {
                        index += offset;
                    }
                    let field_pat_kind = self.resolve_pat_kind(field);
                    let mut mir_const = None;
                    match field_pat_kind {
                        rustc_hir::PatKind::Lit(pat_lit) => match pat_lit.kind {
                            rustc_hir::ExprKind::Lit(expr_lit) => match expr_lit.node {
                                rustc_ast::LitKind::Byte(_)
                                | rustc_ast::LitKind::Char(_)
                                | rustc_ast::LitKind::Int(_, _) => {
                                    // let lit_str =
                                    //     SourceInfo::from_span(expr_lit.span, &self.span_re)
                                    //         .get_string();
                                    let lit_ty = self.typeck_res.node_type(pat_lit.hir_id);
                                    let param_ty = ty::ParamEnv::reveal_all().and(lit_ty);
                                    let width = self.tcx.layout_of(param_ty).unwrap().size;
                                    // println!("Field type layout: {:?}", layout);
                                    mir_const =
                                        Some(self.lit_to_constant(&expr_lit.node, width, false));
                                    // println!("Literal: {}, mir_const: {:?}", lit_str, mir_const);
                                }
                                _ => {}
                            },
                            rustc_hir::ExprKind::Unary(op, expr) => {
                                assert_eq!(op, rustc_hir::UnOp::Neg);
                                if let rustc_hir::ExprKind::Lit(expr_lit) = expr.kind {
                                    match expr_lit.node {
                                        rustc_ast::LitKind::Int(_, _) => {
                                            // let lit_str =
                                            //     SourceInfo::from_span(expr_lit.span, &self.span_re)
                                            //         .get_string();
                                            let lit_ty = self.typeck_res.node_type(pat_lit.hir_id);
                                            let param_ty = ty::ParamEnv::reveal_all().and(lit_ty);
                                            let width = self.tcx.layout_of(param_ty).unwrap().size;
                                            // println!("Field type layout: {:?}", layout);
                                            mir_const = Some(self.lit_to_constant(
                                                &expr_lit.node,
                                                width,
                                                true,
                                            ));
                                            // println!(
                                            //     "Literal: -{}, mir_const: {:?}",
                                            //     lit_str, mir_const
                                            // );
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
                    lit_map.insert(index, mir_const);
                    index += 1;
                }
                let patt = Patt {
                    pat_str: pat_source.get_string(),
                    kind: PattKind::StructLike(lit_map),
                };
                map.insert(pat_source, patt);
            }
            rustc_hir::PatKind::Wild => {
                let patt = Patt {
                    pat_str: pat_source.get_string(),
                    kind: PattKind::Wild,
                };
                map.insert(pat_source, patt);
            }
            _ => {
                panic!("pat.kind is: {:?}", pat.kind);
            }
        }
        map
    }

    fn handle_other_pat(&self, pat: &'tcx rustc_hir::Pat<'tcx>) -> HashMap<SourceInfo, Patt> {
        let mut map = HashMap::new();
        let pat_source = SourceInfo::from_span(pat.span, &self.span_re);
        let pat_kind = self.resolve_pat_kind(pat);
        match pat_kind {
            rustc_hir::PatKind::Or(subpats) => {
                for subpat in subpats {
                    map.extend(self.handle_other_pat(subpat));
                }
            }
            rustc_hir::PatKind::Lit(pat_lit) => {
                let mut mir_const = None;
                match pat_lit.kind {
                    rustc_hir::ExprKind::Lit(expr_lit) => match expr_lit.node {
                        rustc_ast::LitKind::Byte(_)
                        | rustc_ast::LitKind::Char(_)
                        | rustc_ast::LitKind::Int(_, _) => {
                            // let lit_str =
                            //     SourceInfo::from_span(expr_lit.span, &self.span_re).get_string();
                            let lit_ty = self.typeck_res.node_type(pat_lit.hir_id);
                            let param_ty = ty::ParamEnv::reveal_all().and(lit_ty);
                            let width = self.tcx.layout_of(param_ty).unwrap().size;
                            // println!("Field type layout: {:?}", layout);
                            mir_const = Some(self.lit_to_constant(&expr_lit.node, width, false));
                            // println!("Literal: {}, mir_const: {:?}", lit_str, mir_const);
                        }
                        _ => {}
                    },
                    rustc_hir::ExprKind::Unary(op, expr) => {
                        assert_eq!(op, rustc_hir::UnOp::Neg);
                        if let rustc_hir::ExprKind::Lit(expr_lit) = expr.kind {
                            match expr_lit.node {
                                rustc_ast::LitKind::Int(_, _) => {
                                    // let lit_str =
                                    //     SourceInfo::from_span(expr_lit.span, &self.span_re)
                                    //         .get_string();
                                    let lit_ty = self.typeck_res.node_type(pat_lit.hir_id);
                                    let param_ty = ty::ParamEnv::reveal_all().and(lit_ty);
                                    let width = self.tcx.layout_of(param_ty).unwrap().size;
                                    // println!("Field type layout: {:?}", layout);
                                    mir_const =
                                        Some(self.lit_to_constant(&expr_lit.node, width, true));
                                    // println!("Literal: -{}, mir_const: {:?}", lit_str, mir_const);
                                }
                                _ => {}
                            }
                        } else {
                            panic!("expr.kind is: {:?}", expr.kind);
                        }
                    }
                    _ => {}
                }
                let patt = Patt {
                    pat_str: pat_source.get_string(),
                    kind: PattKind::Other(mir_const),
                };
                map.insert(pat_source, patt);
            }
            rustc_hir::PatKind::Wild => {
                let patt = Patt {
                    pat_str: pat_source.get_string(),
                    kind: PattKind::Wild,
                };
                map.insert(pat_source, patt);
            }
            _ => {
                let patt = Patt {
                    pat_str: pat_source.get_string(),
                    kind: PattKind::Other(None),
                };
                map.insert(pat_source, patt);
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
                        let cond_map = self.handle_expr(guard);
                        self.source_cond_map.extend(cond_map.clone());
                        guard_map = Some(cond_map);
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
            TyKind::Tuple(tuple_def) => {
                for arm in arms {
                    let patt_map = self.handle_tuple_pat(arm.pat, tuple_def);
                    let mut guard_map = None;
                    if let Some(guard) = &arm.guard {
                        let cond_map = self.handle_expr(guard);
                        self.source_cond_map.extend(cond_map.clone());
                        guard_map = Some(cond_map);
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
                for arm in arms {
                    let patt_map = self.handle_other_pat(arm.pat);
                    let mut guard_map = None;
                    if let Some(guard) = &arm.guard {
                        let cond_map = self.handle_expr(guard);
                        self.source_cond_map.extend(cond_map.clone());
                        guard_map = Some(cond_map);
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
        }
        self.source_cond_map
            .insert(match_source, Condition::Match(cond));
    }
}

impl<'tcx> HIRVisitor<'tcx> for BranchVisitor<'tcx> {
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
