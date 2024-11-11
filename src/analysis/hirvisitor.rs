use super::branchvisitor::BranchVisitor;
use super::condition::Condition;
use super::sourceinfo::SourceInfo;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{self, BodyId, FnDecl};
use rustc_middle::hir::map::Map;
use rustc_middle::hir::nested_filter;
use rustc_middle::mir::BasicBlocks;
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::sym;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fs::{self, File};
use std::io::Write;
use syn::parse_str;

fn is_valid_code(code: &str) -> bool {
    parse_str::<syn::Item>(code).is_ok()
}

pub struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    hir_map: Map<'tcx>,
    result: Vec<(
        String,
        SourceInfo,
        BasicBlocks<'tcx>,
        HashMap<SourceInfo, Vec<Condition>>,
    )>,
}

impl<'tcx> HirVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, hir_map: Map<'tcx>) -> Self {
        HirVisitor {
            tcx,
            hir_map,
            result: Vec::new(),
        }
    }

    pub fn move_result(
        self,
    ) -> Vec<(
        String,
        SourceInfo,
        BasicBlocks<'tcx>,
        HashMap<SourceInfo, Vec<Condition>>,
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
        let fn_name = format!("{:?}", id);
        info!("Visiting function: {}", fn_name);

        // Skip functions that are automatically derived
        for parent in self.hir_map.parent_id_iter(b.hir_id) {
            let attrs = self.hir_map.attrs(parent);
            if attrs
                .iter()
                .any(|attr| attr.has_name(sym::automatically_derived))
            {
                warn!("Skip because it is automatically derived");
                return;
            }
        }

        // Skip functions that are not valid code
        let fn_source = SourceInfo::from_span(span, self.tcx.sess.source_map());
        let code = fn_source.get_string();
        if !is_valid_code(&code) {
            warn!("Skip because it is not valid code");
            return;
        }

        // write function source code to file
        let dir_path = format!("./rbrinfo/{}", fn_name);
        let file_path = format!("{}/code.rs", dir_path);
        fs::create_dir_all(dir_path).unwrap();
        let mut file = File::create(file_path).unwrap();
        file.write_all(code.as_bytes()).unwrap();

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
        let mut visitor = BranchVisitor::new(
            self.tcx,
            fn_name.clone(),
            fn_source.clone(),
            self.tcx.typeck(hir.id().hir_id.owner),
        );
        intravisit::walk_body::<BranchVisitor>(&mut visitor, &hir);
        visitor.output_map();

        self.result.push((
            fn_name,
            fn_source,
            mir.basic_blocks.clone(),
            visitor.move_map(),
        ));

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
