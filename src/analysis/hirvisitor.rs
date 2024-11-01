use super::branchvisitor::BranchVisitor;
use super::condition::Condition;
use super::sourceinfo::SourceInfo;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{self, BodyId, FnDecl};
use rustc_middle::hir::map::Map;
use rustc_middle::hir::nested_filter;
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::sym;
use std::collections::HashMap;
use std::fs::{self, File};
use std::io::Write;

pub struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    hir_map: Map<'tcx>,
    span_re: regex::Regex,
    result: Vec<(
        String,
        rustc_middle::mir::BasicBlocks<'tcx>,
        HashMap<SourceInfo, Condition>,
    )>,
}

impl<'tcx> HirVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, hir_map: Map<'tcx>, span_re: regex::Regex) -> Self {
        HirVisitor {
            tcx,
            hir_map,
            span_re,
            result: Vec::new(),
        }
    }

    pub fn move_result(
        self,
    ) -> Vec<(
        String,
        rustc_middle::mir::BasicBlocks<'tcx>,
        HashMap<SourceInfo, Condition>,
    )> {
        self.result
    }
}

impl<'tcx> Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.hir_map
    }

    fn visit_fn(
        &mut self,
        _fk: intravisit::FnKind<'tcx>,
        _fd: &'tcx FnDecl<'tcx>,
        b: BodyId,
        span: rustc_span::Span,
        id: rustc_hir::def_id::LocalDefId,
    ) -> Self::Result {
        let source_map = self.tcx.sess.source_map();
        let lo = source_map.lookup_char_pos(span.lo());
        let hi = source_map.lookup_char_pos(span.hi());
        println!("fn: {:?} at {:?} {:?}", id, lo, hi);

        let parent_id = self.tcx.parent_hir_id(b.hir_id);
        let parent_id = self.tcx.parent_hir_id(parent_id);
        let attrs = self.hir_map.attrs(parent_id);
        if attrs
            .iter()
            .any(|attr| attr.has_name(sym::automatically_derived))
        {
            return;
        }

        let fn_name = format!("{:?}", id);
        info!("Visiting function: {}", fn_name);

        let hir = self.hir_map.body(b);
        let mir = self.tcx.mir_built(id).borrow();

        // write HIR to file
        let dir_path = format!("./rbrinfo/{}", fn_name);
        let file_path = format!("{}/hir.txt", dir_path);
        fs::create_dir_all(dir_path).unwrap();
        let mut file = File::create(file_path).unwrap();
        let buf = format!("{:#?}", hir);
        file.write_all(buf.as_bytes()).unwrap();

        // tranverse HIR
        let fn_source = SourceInfo::from_span(span, &self.span_re);
        let mut visitor = BranchVisitor::new(
            self.tcx,
            fn_name.clone(),
            fn_source,
            self.span_re.clone(),
            self.tcx.typeck(hir.id().hir_id.owner),
        );
        intravisit::walk_body::<BranchVisitor>(&mut visitor, &hir);
        visitor.output_map();

        self.result
            .push((fn_name, mir.basic_blocks.clone(), visitor.move_map()));

        // intravisit::walk_fn(self, fk, fd, b, id);
    }

    // fn visit_impl_item(&mut self, ii: &'tcx rustc_hir::ImplItem<'tcx>) -> Self::Result {
    //     if let ImplItemKind::Fn(sig, body_id) = ii.kind {
    //         // Do something with the function
    //         println!("impl Function: {:?}", ii.ident);
    //     }
    //     intravisit::walk_impl_item(self, ii);
    // }

    // fn visit_item(&mut self, i: &'tcx rustc_hir::Item<'tcx>) -> Self::Result {
    //     if let ItemKind::Fn(sig, _, body_id) = i.kind {
    //         // Do something with the function
    //         println!("item Function: {:?}", i.ident);
    //     }
    //     if let ItemKind::Impl(impl_) = i.kind {
    //         // Do something with the function
    //         println!("item Impl: {:?}", i.ident);
    //         let attrs = self.hir_map.attrs(i.hir_id());
    //         println!("id: {:?}", i.hir_id());
    //         println!("Item: {:#?}", i);
    //         println!("attrs: {:?}", attrs);
    //     }
    //     intravisit::walk_item(self, i);
    // }
}
