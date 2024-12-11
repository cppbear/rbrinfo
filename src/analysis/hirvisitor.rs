use super::branchvisitor::BranchVisitor;
use super::condition::Condition;
use super::exporter::ModInfo;
use super::sourceinfo::SourceInfo;
use rustc_hir::def_id::CRATE_DEF_ID;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{self, BodyId, FnDecl};
use rustc_middle::hir::map::Map;
use rustc_middle::hir::nested_filter;
use rustc_middle::mir::BasicBlocks;
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::sym;
use std::collections::{HashMap, HashSet};
use std::fs::{self, File};
use std::io::Write;
use syn::parse_str;

fn is_valid_code(code: &str) -> bool {
    parse_str::<syn::Item>(code).is_ok()
}

pub struct VisitorData<'tcx> {
    pub id: String,
    pub fn_name: String,
    pub has_ret: bool,
    pub mod_info: ModInfo,
    pub visible: bool,
    pub fn_source: SourceInfo,
    pub basic_blocks: BasicBlocks<'tcx>,
    pub cond_map: HashMap<SourceInfo, HashSet<Condition>>,
}

pub struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    hir_map: Map<'tcx>,
    mod_infos: Vec<ModInfo>,
    result: Vec<VisitorData<'tcx>>,
}

impl<'tcx> HirVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, hir_map: Map<'tcx>) -> Self {
        HirVisitor {
            tcx,
            hir_map,
            mod_infos: Vec::new(),
            result: Vec::new(),
        }
    }

    pub fn move_result(self) -> Vec<VisitorData<'tcx>> {
        self.result
    }

    fn is_accessible_from_crate(
        &self,
        def_id: rustc_hir::def_id::DefId,
        source: &SourceInfo,
    ) -> bool {
        let visibility = self.tcx.visibility(def_id);
        visibility.is_accessible_from(CRATE_DEF_ID.to_def_id(), self.tcx)
            && !source.get_file().contains("main.rs")
    }
}

impl<'tcx> Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.hir_map
    }

    fn visit_mod(
        &mut self,
        m: &'tcx rustc_hir::Mod<'tcx>,
        _s: rustc_span::Span,
        n: rustc_hir::HirId,
    ) -> Self::Result {
        let mod_source = SourceInfo::from_span(_s, self.tcx.sess.source_map());
        let def_id = n.owner.to_def_id();
        let module_name = self.tcx.def_path_str(def_id);
        info!("Visiting module: {}, {:?}", module_name, mod_source);
        self.mod_infos.push(ModInfo {
            name: module_name.clone(),
            loc: mod_source,
        });
        intravisit::walk_mod(self, m, n);
        info!("Leaving module: {}", module_name);
        self.mod_infos.pop();
    }

    fn visit_fn(
        &mut self,
        _fk: intravisit::FnKind<'tcx>,
        _fd: &'tcx FnDecl<'tcx>,
        b: BodyId,
        span: rustc_span::Span,
        id: rustc_hir::def_id::LocalDefId,
    ) -> Self::Result {
        let id_str = format!("{:?}", id);
        let def_id = id.to_def_id();
        let mut fn_name = self.tcx.crate_name(def_id.krate).to_string();
        fn_name.push_str(&self.tcx.def_path(def_id).to_string_no_crate_verbose());
        info!("Visiting function: {}, name: {}", id_str, fn_name);

        let mod_info = self.mod_infos.last().unwrap();
        let has_ret = matches!(_fd.output, rustc_hir::FnRetTy::Return(_));

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
        let dir_path = format!("./rbrinfo/{}", id_str);
        let file_path = format!("{}/code.rs", dir_path);
        fs::create_dir_all(dir_path).unwrap();
        let mut file = File::create(file_path).unwrap();
        file.write_all(code.as_bytes()).unwrap();

        let hir = self.hir_map.body(b);
        let mir = self.tcx.mir_built(id).borrow();

        // write HIR to file
        let dir_path = format!("./rbrinfo/{}", id_str);
        let file_path = format!("{}/hir.txt", dir_path);
        fs::create_dir_all(dir_path).unwrap();
        let mut file = File::create(file_path).unwrap();
        let buf = format!("{:#?}", hir);
        file.write_all(buf.as_bytes()).unwrap();

        // tranverse HIR
        let mut visitor = BranchVisitor::new(
            self.tcx,
            id_str.clone(),
            fn_name.clone(),
            fn_source.clone(),
            self.tcx.typeck(hir.id().hir_id.owner),
        );
        intravisit::walk_body::<BranchVisitor>(&mut visitor, &hir);
        visitor.output_map();

        // check visibility
        let visible = self.is_accessible_from_crate(def_id, &fn_source);

        let data = VisitorData {
            id: id_str,
            fn_name,
            has_ret,
            mod_info: mod_info.clone(),
            visible,
            fn_source,
            basic_blocks: mir.basic_blocks.clone(),
            cond_map: visitor.move_map(),
        };

        self.result.push(data);

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
