use super::condition::{Arm, BoolCond, Condition, MatchCond, MatchKind, PattKind};
use super::hirvisitor::HirVisitor;
use super::option::AnalysisOption;
use super::sourceinfo::SourceInfo;
use petgraph::dot::Config;
use petgraph::dot::Dot;
use petgraph::graph::DiGraph;
use petgraph::prelude::*;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_data_structures::graph::StartNode;
use rustc_driver::Compilation;
use rustc_interface::interface;
use rustc_interface::Queries;
use rustc_middle::mir::{BasicBlock, Operand};
use rustc_middle::mir::{Statement, SwitchTargets};
use rustc_middle::mir::{Terminator, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::SourceMap;
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use std::fs::{self, File};
use std::io::Write;

pub struct MirCheckerCallbacks {
    pub analysis_options: AnalysisOption,
    pub source_name: String,
    // cond_map: HashMap<SourceInfo, Condition>,
}

impl MirCheckerCallbacks {
    pub fn new(options: AnalysisOption) -> Self {
        Self {
            analysis_options: options,
            source_name: String::new(),
            // cond_map: HashMap::new(),
        }
    }
}

impl rustc_driver::Callbacks for MirCheckerCallbacks {
    /// Called before creating the compiler instance
    fn config(&mut self, config: &mut interface::Config) {
        self.source_name = format!("{:?}", config.input.source_name());
        config.crate_cfg.push("mir_checker".to_string());
        info!("Source file: {}", self.source_name);
    }

    // fn after_crate_root_parsing<'tcx>(
    //     &mut self,
    //     _compiler: &interface::Compiler,
    //     _queries: &'tcx Queries<'tcx>,
    // ) -> Compilation {
    //     _queries
    //         .global_ctxt()
    //         .unwrap()
    //         .enter(|tcx| self.run_analysis(tcx));

    //     Compilation::Continue
    // }

    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        _queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        _queries
            .global_ctxt()
            .unwrap()
            .enter(|tcx| self.run_analysis(tcx));

        Compilation::Continue
    }
}

#[derive(Clone, Debug)]
struct MyBlock<'a> {
    block_name: BasicBlock,
    statements: Vec<Statement<'a>>,
    terminator: Terminator<'a>,
    pre_blocks: Vec<BasicBlock>,
    suc_blocks: Vec<BasicBlock>,
}

#[derive(Clone, Debug)]
struct DFSCxt {
    block: BasicBlock,
    path: Vec<BasicBlock>,
    conds: Vec<(String, String)>,
    branches: HashSet<(BasicBlock, BasicBlock)>,
    loop_paths: Vec<Vec<BasicBlock>>,
}

impl DFSCxt {
    fn new(
        block: BasicBlock,
        path: Vec<BasicBlock>,
        conds: Vec<(String, String)>,
        branches: HashSet<(BasicBlock, BasicBlock)>,
        loop_paths: Vec<Vec<BasicBlock>>,
    ) -> Self {
        Self {
            block,
            path,
            conds,
            branches,
            loop_paths,
        }
    }
}

fn count_subsequence<T: PartialEq>(vec: &Vec<T>, subseq: &Vec<T>) -> usize {
    if subseq.is_empty() || vec.len() < subseq.len() {
        return 0;
    }

    let mut count = 0;
    for window in vec.windows(subseq.len()) {
        if window == subseq {
            count += 1;
        }
    }
    count
}

fn remove_subsequence<T: PartialEq>(vec: &mut Vec<T>, subseq: &Vec<T>) {
    if subseq.is_empty() || subseq.len() > vec.len() {
        return;
    }

    let seq_len = subseq.len();
    let mut i = 0;

    while vec.len() > seq_len && i <= vec.len() - seq_len {
        if &vec[i..i + seq_len] == subseq {
            vec.drain(i..i + seq_len);
        } else {
            i += 1;
        }
    }
}

#[derive(Clone)]
struct FnBlocks<'a> {
    fn_name: String,
    fn_source: SourceInfo,
    start_node: BasicBlock,
    blocks: Vec<MyBlock<'a>>,
    dominators: Dominators<BasicBlock>,
    cond_chains: Vec<(Vec<(String, String)>, Vec<BasicBlock>)>,
    source_map: &'a SourceMap,
    cond_map: HashMap<SourceInfo, Vec<Condition>>,
}

impl FnBlocks<'_> {
    const MAX_CONDITIONS: usize = 9999;

    fn get_source_info(&self, span: rustc_span::Span) -> SourceInfo {
        SourceInfo::from_span(span, self.source_map)
    }

    fn get_matched_cond(
        &self,
        source_info: &SourceInfo,
        bb: BasicBlock,
    ) -> Option<(Condition, Option<Vec<SourceInfo>>)> {
        if let Some(cond) = self.cond_map.get(source_info) {
            if cond.len() == 1 {
                return Some((cond[0].clone(), None));
            } else {
                for c in cond {
                    if self.block_contains_cond(bb, source_info) {
                        return Some((c.clone(), None));
                    }
                    if let Condition::Match(match_cond) = c {
                        if self.block_contains_cond(bb, &match_cond.match_source) {
                            return Some((c.clone(), None));
                        }
                    }
                }
                return None;
            }
        }

        for (k, v) in &self.cond_map {
            if source_info.contains(k) || k.contains(source_info) {
                if v.len() == 1 {
                    return Some((v[0].clone(), None));
                } else {
                    for c in v {
                        if self.block_contains_cond(bb, k) {
                            return Some((c.clone(), None));
                        }
                        if let Condition::Match(match_cond) = c {
                            if self.block_contains_cond(bb, &match_cond.match_source) {
                                return Some((c.clone(), None));
                            }
                        }
                    }
                    return None;
                }
            }
            for c in v {
                if let Condition::Match(match_cond) = c {
                    let mut sources = vec![];
                    for (pat_source, _) in &match_cond.arms {
                        if source_info.contains(pat_source) || pat_source.contains(source_info) {
                            // Terminator of kind falseEdge may contain multiple patterns
                            sources.push(pat_source.clone());
                        }
                    }
                    if !sources.is_empty() {
                        return Some((c.clone(), Some(sources)));
                    }
                }
            }
        }

        None
    }

    fn block_contains_cond(&self, bb: BasicBlock, source: &SourceInfo) -> bool {
        let block = &self.blocks[bb.index()];
        for stmt in block.statements.iter().rev() {
            let stmt_source = self.get_source_info(stmt.source_info.span);
            if self.fn_source.contains(&stmt_source) {
                if source.contains(&stmt_source) || stmt_source.contains(source) {
                    return true;
                }
            }
        }

        false
    }

    fn block_in_arm(&self, block: &MyBlock, arm: &Arm) -> bool {
        if let Some(body_source) = &arm.body_source {
            for stmt in &block.statements {
                if body_source.contains(&self.get_source_info(stmt.source_info.span)) {
                    return true;
                }
            }

            if body_source.contains(&self.get_source_info(block.terminator.source_info.span)) {
                return true;
            }
        }

        false
    }

    fn mir_out(&self) {
        let mut mir_str = String::new();
        for block in &self.blocks {
            mir_str.push_str(&format!("{:?}\n", block.block_name));
            let mut i = 0;
            for statement in &block.statements {
                mir_str.push_str(&format!("  {}: {:?}\n", i, statement));
                let stmt_source = self.get_source_info(statement.source_info.span);
                mir_str.push_str(&format!("    {:?}\n", stmt_source));
                i = i + 1;
            }
            let ter_source = self.get_source_info(block.terminator.source_info.span);
            let formatted = format!(
                "Terminator {{\n    source_info: {:?}\n    kind: {:#?}\n}}\n",
                ter_source, block.terminator.kind
            );
            let spaces = " ".repeat(2);
            let ternimator: String = formatted
                .lines()
                .map(|line| format!("{}{}", spaces, line))
                .collect::<Vec<String>>()
                .join("\n");
            mir_str.push_str(&format!("{}\n", ternimator));
            mir_str.push_str(&format!("  preds {:?}\n", block.pre_blocks));
            mir_str.push_str(&format!("  succs {:?}\n", block.suc_blocks));
            mir_str.push_str("\n");
        }
        let dir_path = format!("./rbrinfo/{}", self.fn_name);
        let file_path = format!("{}/mir.txt", dir_path);
        fs::create_dir_all(dir_path).unwrap();
        let mut file = File::create(file_path).unwrap();
        file.write_all(mir_str.as_bytes()).unwrap();
    }

    fn handle_enum_match(
        &self,
        stack: &mut Vec<DFSCxt>,
        dfs_cxt: &DFSCxt,
        targets: &SwitchTargets,
        match_cond: &MatchCond,
        arm_source: &Option<Vec<SourceInfo>>,
    ) {
        let DFSCxt {
            block,
            path,
            conds,
            branches,
            loop_paths,
        } = dfs_cxt;
        let block_name = *block;
        if let Some(pat_sources) = arm_source {
            // Span of Terminator points to a arm pattern
            error!("Span of Terminator for Enum points to an arm pattern, this is NOT common. Check {:?}", block_name);
            // FIXME: handle matches! macro
            assert_eq!(pat_sources.len(), 1);
            let arm = match_cond.arms.get(&pat_sources[0]).unwrap();
            // common branches
            for (value, target) in targets.iter() {
                let mut branches = branches.clone();
                if branches.insert((block_name, target)) {
                    // new branch
                    let mut path = path.clone();
                    let mut conds = conds.clone();

                    match arm.pat.kind {
                        PattKind::Enum(index) => {
                            if value == index as u128 {
                                conds.push((
                                    format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                    "true".to_string(),
                                ));
                            }
                        }
                        PattKind::Wild => {
                            error!(
                                "Span of Terminator points to _ pattern. Check {:?}",
                                block_name
                            );
                        }
                        PattKind::Other(_) => {}
                        _ => {
                            panic!(
                                "Invalid pattern kind for Enum. Check Arm of {:?}",
                                pat_sources[0]
                            );
                        }
                    }

                    path.push(target);
                    stack.push(DFSCxt::new(
                        target,
                        path,
                        conds,
                        branches,
                        loop_paths.clone(),
                    ));
                }
            }
            // otherwise branch
            let mut branches = branches.clone();
            if !matches!(
                self.blocks[targets.otherwise().index()].terminator.kind,
                TerminatorKind::Unreachable
            ) && branches.insert((block_name, targets.otherwise()))
            {
                // new branch
                let mut path = path.clone();
                let mut conds = conds.clone();

                match arm.pat.kind {
                    PattKind::Enum(_) => {
                        conds.push((
                            format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                            "false".to_string(),
                        ));
                    }
                    PattKind::Wild => {
                        error!(
                            "Span of Terminator points to _ pattern. Check {:?}",
                            block_name
                        );
                    }
                    PattKind::Other(_) => {}
                    _ => {
                        panic!(
                            "Invalid pattern kind for Enum. Check Arm of {:?}",
                            pat_sources[0]
                        );
                    }
                }

                path.push(targets.otherwise());
                stack.push(DFSCxt::new(
                    targets.otherwise(),
                    path,
                    conds,
                    branches,
                    loop_paths.clone(),
                ));
            }
        } else {
            // Span of Terminator does NOT point to a arm pattern, just "match XXX"
            // info!("Span of Terminator does NOT point to a arm pattern");
            //common branches
            for (value, target) in targets.iter() {
                let mut branches = branches.clone();
                if branches.insert((block_name, target)) {
                    // new branch
                    let mut path = path.clone();
                    let mut conds = conds.clone();

                    let mut found = false;
                    for (arm_source, arm) in &match_cond.arms {
                        match arm.pat.kind {
                            PattKind::Enum(index) => {
                                if value == index as u128 {
                                    conds.push((
                                        format!(
                                            "{} matches {}",
                                            match_cond.match_str, arm.pat.pat_str
                                        ),
                                        "true".to_string(),
                                    ));
                                    found = true;
                                    break;
                                }
                            }
                            PattKind::Wild => {}
                            PattKind::Other(_) => {}
                            _ => {
                                panic!(
                                    "Invalid pattern kind for Enum. Check Arm of {:?}",
                                    arm_source
                                );
                            }
                        }
                    }
                    if !found {
                        error!(
                            "No matched arm found for Enum branch {:?} -> {:?}",
                            block_name, target
                        );
                        // Check if the target block is in the arm body
                        for (_, arm) in &match_cond.arms {
                            if self.block_in_arm(&self.blocks[target.index()], arm) {
                                conds.push((
                                    format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                    "true".to_string(),
                                ));
                                break;
                            }
                        }
                    }

                    path.push(target);
                    stack.push(DFSCxt::new(
                        target,
                        path,
                        conds,
                        branches,
                        loop_paths.clone(),
                    ));
                }
            }
            // otherwise branch
            let mut branches = branches.clone();
            if !matches!(
                self.blocks[targets.otherwise().index()].terminator.kind,
                TerminatorKind::Unreachable
            ) && branches.insert((block_name, targets.otherwise()))
            {
                // new branch
                let mut path = path.clone();
                let mut conds = conds.clone();

                let mut found = false;
                for (arm_source, arm) in &match_cond.arms {
                    match arm.pat.kind {
                        PattKind::Enum(_) => {
                            conds.push((
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "false".to_string(),
                            ));
                            found = true;
                        }
                        PattKind::Wild => {
                            conds.push((
                                format!("{} matches _", match_cond.match_str),
                                "true".to_string(),
                            ));
                            found = true;
                        }
                        PattKind::Other(_) => {}
                        _ => {
                            panic!(
                                "Invalid pattern kind for Enum. Check Arm of {:?}",
                                arm_source
                            );
                        }
                    }
                }
                if !found {
                    error!(
                        "No matched arm found for Enum branch {:?} -> {:?}",
                        block_name,
                        targets.otherwise()
                    );
                    // Check if the target block is in the arm body
                    for (_, arm) in &match_cond.arms {
                        if self.block_in_arm(&self.blocks[targets.otherwise().index()], arm) {
                            conds.push((
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "true".to_string(),
                            ));
                            break;
                        }
                    }
                }

                path.push(targets.otherwise());
                stack.push(DFSCxt::new(
                    targets.otherwise(),
                    path,
                    conds,
                    branches,
                    loop_paths.clone(),
                ));
            }
        }
    }

    fn handle_structlike_match(
        &self,
        stack: &mut Vec<DFSCxt>,
        dfs_cxt: &DFSCxt,
        cond_source: &SourceInfo,
        discr: &Operand,
        targets: &SwitchTargets,
        match_cond: &MatchCond,
        arm_source: &Option<Vec<SourceInfo>>,
    ) {
        let DFSCxt {
            block,
            path,
            conds,
            branches,
            loop_paths,
        } = dfs_cxt;
        let block_name = *block;
        if let Some(pat_sources) = arm_source {
            // Span of Terminator points to a arm pattern
            // info!("Span of Terminator points to a arm pattern");
            assert_eq!(pat_sources.len(), 1);
            let arm = match_cond.arms.get(&pat_sources[0]).unwrap();
            // common branches
            for (value, target) in targets.iter() {
                let mut branches = branches.clone();
                if branches.insert((block_name, target)) {
                    // new branch
                    let mut path = path.clone();
                    let mut conds = conds.clone();

                    match &arm.pat.kind {
                        PattKind::StructLike(field_map) => {
                            let mut found = false;
                            for (field_index, (lit, field_source)) in field_map {
                                if cond_source == field_source {
                                    info!("Span of Terminator points to field pattern");
                                    if let Some(lit) = lit {
                                        if value != *lit {
                                            error!("Value not equal to literal");
                                        }
                                        conds.push((
                                            format!(
                                                "{}.{} matches {}",
                                                match_cond.match_str,
                                                match_cond.match_kind.get_field_name(*field_index),
                                                field_source.get_string()
                                            ),
                                            "true".to_string(),
                                        ));
                                    } else {
                                        if value != 0 {
                                            error!("Value not equal to 0");
                                        }
                                        conds.push((
                                            format!(
                                                "{}.{} matches {}",
                                                match_cond.match_str,
                                                match_cond.match_kind.get_field_name(*field_index),
                                                field_source.get_string()
                                            ),
                                            "false".to_string(),
                                        ));
                                    }
                                    found = true;
                                    break;
                                }
                            }
                            if !found {
                                info!("Span of Terminator does NOT point to field pattern");
                                match discr {
                                    Operand::Copy(place) | Operand::Move(place) => {
                                        for proj in place.projection.iter() {
                                            if let rustc_middle::mir::ProjectionElem::Field(
                                                idx,
                                                _,
                                            ) = proj
                                            {
                                                let (lit, field_source) =
                                                    field_map.get(&idx.index()).unwrap();
                                                if let Some(lit) = lit {
                                                    if value != *lit {
                                                        error!("Value not equal to literal");
                                                    }
                                                    conds.push((
                                                        format!(
                                                            "{}.{} matches {}",
                                                            match_cond.match_str,
                                                            match_cond
                                                                .match_kind
                                                                .get_field_name(idx.index()),
                                                            field_source.get_string()
                                                        ),
                                                        "true".to_string(),
                                                    ));
                                                } else {
                                                    if value != 0 {
                                                        error!("Value not equal to 0");
                                                    }
                                                    conds.push((
                                                        format!(
                                                            "{}.{} matches {}",
                                                            match_cond.match_str,
                                                            match_cond
                                                                .match_kind
                                                                .get_field_name(idx.index()),
                                                            field_source.get_string()
                                                        ),
                                                        "false".to_string(),
                                                    ));
                                                }
                                                break;
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }
                            // Check if the target block is in the arm body
                            if self.block_in_arm(&self.blocks[target.index()], arm) {
                                conds.push((
                                    format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                    "true".to_string(),
                                ));
                            }
                        }
                        PattKind::Wild => {
                            error!("Span of Terminator points to _ pattern");
                        }
                        PattKind::Other(_) => {}
                        _ => {
                            panic!("Invalid pattern kind for Enum");
                        }
                    }

                    path.push(target);
                    stack.push(DFSCxt::new(
                        target,
                        path,
                        conds,
                        branches,
                        loop_paths.clone(),
                    ));
                }
            }
            // otherwise branch
            let mut branches = branches.clone();
            if !matches!(
                self.blocks[targets.otherwise().index()].terminator.kind,
                TerminatorKind::Unreachable
            ) && branches.insert((block_name, targets.otherwise()))
            {
                // new branch
                let mut path = path.clone();
                let mut conds = conds.clone();

                match &arm.pat.kind {
                    PattKind::StructLike(field_map) => {
                        let mut found = false;
                        for (field_index, (lit, field_source)) in field_map {
                            if cond_source == field_source {
                                info!("Span of Terminator points to field pattern");
                                if let Some(_) = lit {
                                    conds.push((
                                        format!(
                                            "{}.{} matches {}",
                                            match_cond.match_str,
                                            match_cond.match_kind.get_field_name(*field_index),
                                            field_source.get_string()
                                        ),
                                        "false".to_string(),
                                    ));
                                } else {
                                    conds.push((
                                        format!(
                                            "{}.{} matches {}",
                                            match_cond.match_str,
                                            match_cond.match_kind.get_field_name(*field_index),
                                            field_source.get_string()
                                        ),
                                        "true".to_string(),
                                    ));
                                }
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            info!("Span of Terminator does NOT point to field pattern");
                            match discr {
                                Operand::Copy(place) | Operand::Move(place) => {
                                    for proj in place.projection.iter() {
                                        if let rustc_middle::mir::ProjectionElem::Field(idx, _) =
                                            proj
                                        {
                                            if let Some((lit, source)) = field_map.get(&idx.index())
                                            {
                                                if let Some(_) = lit {
                                                    conds.push((
                                                        format!(
                                                            "{}.{} matches {}",
                                                            match_cond.match_str,
                                                            match_cond
                                                                .match_kind
                                                                .get_field_name(idx.index()),
                                                            source.get_string()
                                                        ),
                                                        "false".to_string(),
                                                    ));
                                                } else {
                                                    conds.push((
                                                        format!(
                                                            "{}.{} matches {}",
                                                            match_cond.match_str,
                                                            match_cond
                                                                .match_kind
                                                                .get_field_name(idx.index()),
                                                            source.get_string()
                                                        ),
                                                        "true".to_string(),
                                                    ));
                                                }
                                                break;
                                            }
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                        // Check if the target block is in the arm body
                        if self.block_in_arm(&self.blocks[targets.otherwise().index()], arm) {
                            conds.push((
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "true".to_string(),
                            ));
                        }
                    }
                    PattKind::Wild => {
                        error!("Span of Terminator points to _ pattern");
                    }
                    PattKind::Other(_) => {}
                    _ => {
                        panic!("Invalid pattern kind for Enum");
                    }
                }

                path.push(targets.otherwise());
                stack.push(DFSCxt::new(
                    targets.otherwise(),
                    path,
                    conds,
                    branches,
                    loop_paths.clone(),
                ));
            }
        } else {
            // Span of Terminator does NOT point to a arm pattern, just "match XXX"
            // info!("Span of Terminator does NOT point to a arm pattern");
            // common branches
            for (value, target) in targets.iter() {
                let mut branches = branches.clone();
                if branches.insert((block_name, target)) {
                    // new branch
                    let mut path = path.clone();
                    let mut conds = conds.clone();

                    'arms: for (arm_source, arm) in &match_cond.arms {
                        match &arm.pat.kind {
                            PattKind::StructLike(field_map) => match discr {
                                Operand::Copy(place) | Operand::Move(place) => {
                                    for proj in place.projection.iter() {
                                        if let rustc_middle::mir::ProjectionElem::Field(idx, _) =
                                            proj
                                        {
                                            if let Some((lit, source)) = field_map.get(&idx.index())
                                            {
                                                if let Some(lit) = lit {
                                                    if value == *lit {
                                                        conds.push((
                                                            format!(
                                                                "{}.{} matches {}",
                                                                match_cond.match_str,
                                                                match_cond
                                                                    .match_kind
                                                                    .get_field_name(idx.index()),
                                                                source.get_string()
                                                            ),
                                                            "true".to_string(),
                                                        ));
                                                        break 'arms;
                                                    }
                                                }
                                            }
                                            break;
                                        }
                                    }
                                }
                                _ => {}
                            },
                            PattKind::Wild => {}
                            PattKind::Other(_) => {}
                            _ => {
                                panic!(
                                    "Invalid pattern kind for Enum. Check Arm of {:?}",
                                    arm_source
                                );
                            }
                        }
                    }
                    // Check if the target block is in the arm body
                    for (_, arm) in &match_cond.arms {
                        if self.block_in_arm(&self.blocks[target.index()], arm) {
                            conds.push((
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "true".to_string(),
                            ));
                            break;
                        }
                    }

                    path.push(target);
                    stack.push(DFSCxt::new(
                        target,
                        path,
                        conds,
                        branches,
                        loop_paths.clone(),
                    ));
                }
            }
            // otherwise branch
            let mut cmp_values: Vec<u128> = targets.iter().map(|(v, _)| v).collect();
            let mut branches = branches.clone();
            if !matches!(
                self.blocks[targets.otherwise().index()].terminator.kind,
                TerminatorKind::Unreachable
            ) && branches.insert((block_name, targets.otherwise()))
            {
                // new branch
                let mut path = path.clone();
                let mut conds = conds.clone();

                for (arm_source, arm) in &match_cond.arms {
                    match &arm.pat.kind {
                        PattKind::StructLike(field_map) => match discr {
                            Operand::Copy(place) | Operand::Move(place) => {
                                for proj in place.projection.iter() {
                                    if let rustc_middle::mir::ProjectionElem::Field(idx, _) = proj {
                                        if let Some((lit, source)) = field_map.get(&idx.index()) {
                                            if let Some(lit) = lit {
                                                if cmp_values.contains(lit) {
                                                    cmp_values.retain(|v| v != lit);
                                                    conds.push((
                                                        format!(
                                                            "{}.{} matches {}",
                                                            match_cond.match_str,
                                                            match_cond
                                                                .match_kind
                                                                .get_field_name(idx.index()),
                                                            source.get_string()
                                                        ),
                                                        "false".to_string(),
                                                    ));
                                                }
                                            }
                                        }
                                        break;
                                    }
                                }
                            }
                            _ => {}
                        },
                        PattKind::Wild => {}
                        PattKind::Other(_) => {}
                        _ => {
                            panic!(
                                "Invalid pattern kind for Enum. Check Arm of {:?}",
                                arm_source
                            );
                        }
                    }
                }
                // Check if the target block is in the arm body
                for (_, arm) in &match_cond.arms {
                    if self.block_in_arm(&self.blocks[targets.otherwise().index()], arm) {
                        conds.push((
                            format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                            "true".to_string(),
                        ));
                        break;
                    }
                }

                path.push(targets.otherwise());
                stack.push(DFSCxt::new(
                    targets.otherwise(),
                    path,
                    conds,
                    branches,
                    loop_paths.clone(),
                ));
            }
        }
    }

    fn handle_other_match(
        &self,
        stack: &mut Vec<DFSCxt>,
        dfs_cxt: &DFSCxt,
        targets: &SwitchTargets,
        match_cond: &MatchCond,
        arm_source: &Option<Vec<SourceInfo>>,
    ) {
        let DFSCxt {
            block,
            path,
            conds,
            branches,
            loop_paths,
        } = dfs_cxt;
        let block_name = *block;
        if let Some(pat_sources) = arm_source {
            // Span of Terminator points to a arm pattern
            // info!("Span of Terminator points to a arm pattern");
            assert_eq!(pat_sources.len(), 1);
            let arm = match_cond.arms.get(&pat_sources[0]).unwrap();
            // common branches
            for (value, target) in targets.iter() {
                let mut branches = branches.clone();
                if branches.insert((block_name, target)) {
                    // new branch
                    let mut path = path.clone();
                    let mut conds = conds.clone();

                    match arm.pat.kind {
                        PattKind::Other(lit) => {
                            if let Some(lit) = lit {
                                if value != lit {
                                    error!("Value not equal to literal");
                                }
                                conds.push((
                                    format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                    "true".to_string(),
                                ));
                            } else {
                                if value != 0 {
                                    error!("Value not equal to 0");
                                }
                                conds.push((
                                    format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                    "false".to_string(),
                                ));
                            }
                            // Check if the target block is in the arm body
                            if self.block_in_arm(&self.blocks[target.index()], arm) {
                                conds.push((
                                    format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                    "true".to_string(),
                                ));
                            }
                        }
                        PattKind::Wild => {
                            error!("Span of Terminator points to _ pattern");
                        }
                        _ => {
                            panic!("Invalid pattern kind for Enum");
                        }
                    }

                    path.push(target);
                    stack.push(DFSCxt::new(
                        target,
                        path,
                        conds,
                        branches,
                        loop_paths.clone(),
                    ));
                }
            }
            // otherwise branch
            let mut branches = branches.clone();
            if !matches!(
                self.blocks[targets.otherwise().index()].terminator.kind,
                TerminatorKind::Unreachable
            ) && branches.insert((block_name, targets.otherwise()))
            {
                // new branch
                let mut path = path.clone();
                let mut conds = conds.clone();

                match arm.pat.kind {
                    PattKind::Other(lit) => {
                        if let Some(_) = lit {
                            conds.push((
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "false".to_string(),
                            ));
                        } else {
                            conds.push((
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "true".to_string(),
                            ));
                        }
                        // Check if the target block is in the arm body
                        if self.block_in_arm(&self.blocks[targets.otherwise().index()], arm) {
                            conds.push((
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "true".to_string(),
                            ));
                        }
                    }
                    PattKind::Wild => {
                        error!("Span of Terminator points to _ pattern");
                    }
                    _ => {
                        panic!("Invalid pattern kind for Enum");
                    }
                }

                path.push(targets.otherwise());
                stack.push(DFSCxt::new(
                    targets.otherwise(),
                    path,
                    conds,
                    branches,
                    loop_paths.clone(),
                ));
            }
        } else {
            // Span of Terminator does NOT point to a arm pattern, just "match XXX"
            // info!("Span of Terminator does NOT point to a arm pattern");
            // common branches
            for (value, target) in targets.iter() {
                let mut branches = branches.clone();
                if branches.insert((block_name, target)) {
                    // new branch
                    let mut path = path.clone();
                    let mut conds = conds.clone();

                    for (arm_source, arm) in &match_cond.arms {
                        match &arm.pat.kind {
                            PattKind::Other(lit) => {
                                if let Some(lit) = lit {
                                    if value == *lit {
                                        conds.push((
                                            format!(
                                                "{} matches {}",
                                                match_cond.match_str, arm.pat.pat_str
                                            ),
                                            "true".to_string(),
                                        ));
                                        break;
                                    }
                                } else {
                                    if value == 0 {
                                        warn!(
                                            "Branch {:?} -> {:?}. Arm of {:?}",
                                            block_name, target, arm_source
                                        );
                                        // conds.push((
                                        //     format!(
                                        //         "{} matches {}",
                                        //         match_cond.match_str, arm.pat.pat_str
                                        //     ),
                                        //     "false".to_string(),
                                        // ));
                                        // break;
                                    }
                                }
                            }
                            PattKind::Wild => {}
                            _ => {
                                panic!(
                                    "Invalid pattern kind for Enum. Check Arm of {:?}",
                                    arm_source
                                );
                            }
                        }
                    }
                    // Check if the target block is in the arm body
                    for (_, arm) in &match_cond.arms {
                        if self.block_in_arm(&self.blocks[target.index()], arm) {
                            conds.push((
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "true".to_string(),
                            ));
                            break;
                        }
                    }

                    path.push(target);
                    stack.push(DFSCxt::new(
                        target,
                        path,
                        conds,
                        branches,
                        loop_paths.clone(),
                    ));
                }
            }
            // otherwise branch
            let mut cmp_values: Vec<u128> = targets.iter().map(|(v, _)| v).collect();
            let mut branches = branches.clone();
            if !matches!(
                self.blocks[targets.otherwise().index()].terminator.kind,
                TerminatorKind::Unreachable
            ) && branches.insert((block_name, targets.otherwise()))
            {
                // new branch
                let mut path = path.clone();
                let mut conds = conds.clone();

                for (arm_source, arm) in &match_cond.arms {
                    match &arm.pat.kind {
                        PattKind::Other(lit) => {
                            if let Some(lit) = lit {
                                if cmp_values.contains(lit) {
                                    cmp_values.retain(|v| v != lit);
                                    conds.push((
                                        format!(
                                            "{} matches {}",
                                            match_cond.match_str, arm.pat.pat_str
                                        ),
                                        "false".to_string(),
                                    ));
                                }
                            }
                        }
                        PattKind::Wild => {}
                        _ => {
                            panic!(
                                "Invalid pattern kind for Enum. Check Arm of {:?}",
                                arm_source
                            );
                        }
                    }
                }
                // Check if the target block is in the arm body
                for (_, arm) in &match_cond.arms {
                    if self.block_in_arm(&self.blocks[targets.otherwise().index()], arm) {
                        conds.push((
                            format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                            "true".to_string(),
                        ));
                        break;
                    }
                }

                path.push(targets.otherwise());
                stack.push(DFSCxt::new(
                    targets.otherwise(),
                    path,
                    conds,
                    branches,
                    loop_paths.clone(),
                ));
            }
        }
    }

    fn handle_switchint(
        &self,
        stack: &mut Vec<DFSCxt>,
        dfs_cxt: &DFSCxt,
        ternimator_span: Span,
        discr: &Operand,
        targets: &SwitchTargets,
    ) {
        let DFSCxt {
            block,
            path,
            conds,
            branches,
            loop_paths,
        } = dfs_cxt;
        let block_name = *block;
        let cond_source = self.get_source_info(ternimator_span);
        if let Some((condition, arm_source)) = self.get_matched_cond(&cond_source, block_name) {
            match condition {
                Condition::Bool(bool_cond) => match bool_cond {
                    BoolCond::Binary(bin_cond) => {
                        // common branches
                        for (value, target) in targets.iter() {
                            let mut branches = branches.clone();
                            if branches.insert((block_name, target)) {
                                let mut path = path.clone();
                                let mut conds = conds.clone();

                                if bin_cond.eq_with_int() {
                                    conds.push((bin_cond.get_cond_str(), "true".to_string()));
                                } else if bin_cond.ne_with_int() {
                                    conds.push((bin_cond.get_cond_str(), "false".to_string()));
                                } else {
                                    if value == 0 {
                                        conds.push((bin_cond.get_cond_str(), "false".to_string()));
                                    } else {
                                        conds.push((bin_cond.get_cond_str(), "true".to_string()));
                                    }
                                }

                                path.push(target);
                                stack.push(DFSCxt::new(
                                    target,
                                    path,
                                    conds,
                                    branches,
                                    loop_paths.clone(),
                                ));
                            }
                        }
                        // otherwise branch
                        let mut branches = branches.clone();
                        if !matches!(
                            self.blocks[targets.otherwise().index()].terminator.kind,
                            TerminatorKind::Unreachable
                        ) && branches.insert((block_name, targets.otherwise()))
                        {
                            let mut path = path.clone();
                            let mut conds = conds.clone();

                            if bin_cond.eq_with_int() {
                                conds.push((bin_cond.get_cond_str(), "false".to_string()));
                            } else if bin_cond.ne_with_int() {
                                conds.push((bin_cond.get_cond_str(), "true".to_string()));
                            } else {
                                conds.push((bin_cond.get_cond_str(), "true".to_string()));
                            }

                            path.push(targets.otherwise());
                            stack.push(DFSCxt::new(
                                targets.otherwise(),
                                path,
                                conds,
                                branches,
                                loop_paths.clone(),
                            ));
                        }
                    }
                    BoolCond::Other(cond_str) => {
                        // common branches
                        for (value, target) in targets.iter() {
                            let mut branches = branches.clone();
                            if branches.insert((block_name, target)) {
                                let mut path = path.clone();
                                let mut conds = conds.clone();

                                if value == 0 {
                                    conds.push((cond_str.clone(), "false".to_string()));
                                } else {
                                    conds.push((cond_str.clone(), "true".to_string()));
                                }

                                path.push(target);
                                stack.push(DFSCxt::new(
                                    target,
                                    path,
                                    conds,
                                    branches,
                                    loop_paths.clone(),
                                ));
                            }
                        }
                        // otherwise branch
                        let mut branches = branches.clone();
                        if !matches!(
                            self.blocks[targets.otherwise().index()].terminator.kind,
                            TerminatorKind::Unreachable
                        ) && branches.insert((block_name, targets.otherwise()))
                        {
                            let mut path = path.clone();
                            let mut conds = conds.clone();

                            conds.push((cond_str, "true".to_string()));

                            path.push(targets.otherwise());
                            stack.push(DFSCxt::new(
                                targets.otherwise(),
                                path,
                                conds,
                                branches,
                                loop_paths.clone(),
                            ));
                        }
                    }
                },
                Condition::For(for_cond) => {
                    // common branches
                    for (value, target) in targets.iter() {
                        let mut branches = branches.clone();
                        if branches.insert((block_name, target)) {
                            let mut path = path.clone();
                            let mut conds = conds.clone();

                            let value_str = match value {
                                0 => "false",
                                1 => "true",
                                _ => panic!("Invalid value"),
                            };
                            conds.push((for_cond.get_cond_str(), value_str.to_string()));

                            path.push(target);
                            stack.push(DFSCxt::new(
                                target,
                                path,
                                conds,
                                branches,
                                loop_paths.clone(),
                            ));
                        }
                    }
                    // otherwise branch
                    let mut branches = branches.clone();
                    if !matches!(
                        self.blocks[targets.otherwise().index()].terminator.kind,
                        TerminatorKind::Unreachable
                    ) && branches.insert((block_name, targets.otherwise()))
                    {
                        let mut path = path.clone();
                        let mut conds = conds.clone();

                        conds.push((for_cond.get_cond_str(), "otherwise".to_string()));

                        path.push(targets.otherwise());
                        stack.push(DFSCxt::new(
                            targets.otherwise(),
                            path,
                            conds,
                            branches,
                            loop_paths.clone(),
                        ));
                    }
                }
                Condition::Match(match_cond) => match &match_cond.match_kind {
                    MatchKind::Enum(_) => {
                        self.handle_enum_match(stack, dfs_cxt, targets, &match_cond, &arm_source);
                    }
                    MatchKind::StructLike(_) => {
                        self.handle_structlike_match(
                            stack,
                            dfs_cxt,
                            &cond_source,
                            discr,
                            targets,
                            &match_cond,
                            &arm_source,
                        );
                    }
                    MatchKind::Other => {
                        self.handle_other_match(stack, dfs_cxt, targets, &match_cond, &arm_source);
                    }
                },
                Condition::Try(try_str) => {
                    // common branches
                    for (value, target) in targets.iter() {
                        let mut branches = branches.clone();
                        if branches.insert((block_name, target)) {
                            let mut path = path.clone();
                            let mut conds = conds.clone();

                            let value_str = match value {
                                0 => "Ok/Some",
                                1 => "Err/None",
                                _ => panic!("Invalid value. Check {:?}", block_name),
                            };
                            conds.push((try_str.clone(), value_str.to_string()));

                            path.push(target);
                            stack.push(DFSCxt::new(
                                target,
                                path,
                                conds,
                                branches,
                                loop_paths.clone(),
                            ));
                        }
                    }
                    // otherwise branch
                    let mut branches = branches.clone();
                    if !matches!(
                        self.blocks[targets.otherwise().index()].terminator.kind,
                        TerminatorKind::Unreachable
                    ) && branches.insert((block_name, targets.otherwise()))
                    {
                        let mut path = path.clone();
                        let mut conds = conds.clone();

                        conds.push((try_str.clone(), "otherwise".to_string()));

                        path.push(targets.otherwise());
                        stack.push(DFSCxt::new(
                            targets.otherwise(),
                            path,
                            conds,
                            branches,
                            loop_paths.clone(),
                        ));
                    }
                }
            }
        } else {
            error!(
                "No matched condition found for {:?} in {:?}",
                cond_source, block_name
            );
            // if self.fn_source.contains(&cond_source) {
            //     error!("No matched condition found for {:?}", cond_source);
            // } else {
            //     error!("No matched condition found for {:?}", cond_source);
            // }
            // TODO: handle the case where the discr is const
            // common branches
            for (_, target) in targets.iter() {
                let mut branches = branches.clone();
                if branches.insert((block_name, target)) {
                    let mut path = path.clone();
                    let conds = conds.clone();

                    path.push(target);
                    stack.push(DFSCxt::new(
                        target,
                        path,
                        conds,
                        branches,
                        loop_paths.clone(),
                    ));
                }
            }
            // otherwise branch
            let mut branches = branches.clone();
            if !matches!(
                self.blocks[targets.otherwise().index()].terminator.kind,
                TerminatorKind::Unreachable
            ) && branches.insert((block_name, targets.otherwise()))
            {
                let mut path = path.clone();
                let conds = conds.clone();

                path.push(targets.otherwise());
                stack.push(DFSCxt::new(
                    targets.otherwise(),
                    path,
                    conds,
                    branches,
                    loop_paths.clone(),
                ));
            }
        }
    }

    fn iterative_dfs(&mut self) -> bool {
        let mut stack: Vec<DFSCxt> = Vec::new();
        let dfs_cxt = DFSCxt::new(
            self.start_node,
            vec![self.start_node],
            Vec::new(),
            HashSet::new(),
            Vec::new(),
        );
        stack.push(dfs_cxt);
        while !stack.is_empty() {
            let mut dfs_cxt = stack.pop().unwrap();
            let DFSCxt {
                block,
                path,
                conds,
                branches,
                loop_paths,
            } = &mut dfs_cxt;
            let block_index = block.index();
            let block = &self.blocks[block_index];

            // Check if a loop path is duplicated
            let mut dup_loop = false;
            let mut path2 = path.clone();
            for loop_path in loop_paths.iter() {
                let count = count_subsequence(&path2, loop_path);
                if count > 1 {
                    dup_loop = true;
                }
                remove_subsequence(&mut path2, loop_path);
            }
            if dup_loop {
                continue;
            }

            // Check if the path contains a loop
            let size = path.len();
            if size > 1 && self.dominators.dominates(path[size - 1], path[size - 2]) {
                let index = path[..size - 1]
                    .iter()
                    .rposition(|&x| x == block.block_name)
                    .unwrap();
                loop_paths.push(path[index..size - 1].to_vec());
            }

            // extract the condition
            if block.suc_blocks.is_empty() {
                self.cond_chains.push((conds.clone(), path.clone()));
                if self.cond_chains.len() > Self::MAX_CONDITIONS {
                    error!("Too many condition chains");
                    return false;
                }
            } else {
                let ter_source = block.terminator.source_info;
                match &block.terminator.kind {
                    TerminatorKind::SwitchInt { discr, targets } => {
                        self.handle_switchint(
                            &mut stack,
                            &dfs_cxt,
                            ter_source.span,
                            discr,
                            targets,
                        );
                    }
                    TerminatorKind::FalseEdge { real_target, .. } => {
                        let cond_source = self.get_source_info(ter_source.span);
                        let mut path = path.clone();
                        let mut conds = conds.clone();
                        if let Some((condition, arm_sources)) =
                            self.get_matched_cond(&cond_source, block.block_name)
                        {
                            match condition {
                                Condition::Match(match_cond) => {
                                    if let Some(pat_sources) = arm_sources {
                                        let pat_strs: String = pat_sources
                                            .iter()
                                            .map(|pat_source| {
                                                let arm = match_cond.arms.get(pat_source).unwrap();
                                                arm.pat.pat_str.clone()
                                            })
                                            .collect::<Vec<String>>()
                                            .join(" | ");
                                        conds.push((
                                            format!(
                                                "{} matches {}",
                                                match_cond.match_str, pat_strs
                                            ),
                                            "true".to_string(),
                                        ));
                                    }
                                }
                                _ => {}
                            }
                        }
                        path.push(*real_target);
                        stack.push(DFSCxt::new(
                            *real_target,
                            path,
                            conds,
                            branches.clone(),
                            loop_paths.clone(),
                        ));
                    }
                    _ => {
                        let mut path = path.clone();
                        path.push(block.suc_blocks[0]);
                        stack.push(DFSCxt::new(
                            block.suc_blocks[0],
                            path,
                            conds.clone(),
                            branches.clone(),
                            loop_paths.clone(),
                        ));
                    }
                }
            }
        }

        true
    }

    fn dump_to_json(&self) {
        let mut json_map = serde_json::Map::new();
        let mut id = 1;
        for (conds, path) in &self.cond_chains {
            let chain_id = format!("{:04}", id);
            let mut chain_map = serde_json::Map::new();
            chain_map.insert("conds".to_string(), serde_json::json!(conds));
            chain_map.insert(
                "path".to_string(),
                serde_json::json!(path.iter().map(|x| x.index()).collect::<Vec<usize>>()),
            );
            json_map.insert(chain_id, serde_json::json!(chain_map));
            id += 1;
        }

        let dir_path = "./rbrinfo/cond_chains";
        let file_path = format!("{}/{}.json", dir_path, self.fn_name);
        fs::create_dir_all(dir_path).unwrap();
        let json = serde_json::to_string_pretty(&json_map).unwrap();
        let mut file = File::create(file_path).unwrap();
        file.write_all(json.as_bytes()).unwrap();
    }

    fn dump_cfg_to_dot(&self) {
        let mut graph = DiGraph::<String, String>::new();

        for block in self.blocks.clone() {
            // let label = format!(
            //     "{:?}\n{:#?}\n{:#?}",
            //     block.block_name, block.statements, block.terminator
            // );
            let label = format!("{:?}", block.block_name);
            graph.add_node(label);
        }

        for block in self.blocks.clone() {
            for succ in block.suc_blocks {
                graph.add_edge(
                    NodeIndex::new(block.block_name.index()),
                    NodeIndex::new(succ.index()),
                    "".to_string(),
                );
            }
        }

        // 用Graphviz Dot格式输出并写入文件
        let dot = Dot::with_config(&graph, &[Config::EdgeNoLabel]);
        let mut file = File::create(format!("rbrinfo/{}/cfg.dot", self.fn_name)).unwrap();
        writeln!(file, "{:#}", dot).unwrap();
    }
}

impl MirCheckerCallbacks {
    fn run_analysis<'tcx, 'compiler>(&mut self, tcx: TyCtxt<'tcx>) {
        let hir_map = tcx.hir();
        let mut visitor = HirVisitor::new(tcx, hir_map);
        hir_map.visit_all_item_likes_in_crate(&mut visitor);
        let result = visitor.move_result();

        let mut ret: Vec<FnBlocks> = vec![];
        for (fn_name, fn_source, basic_blocks, cond_map) in result {
            let mut fn_blocks: Vec<MyBlock> = vec![];
            let blocks: &rustc_middle::mir::BasicBlocks<'_> = &basic_blocks;
            let pre_blocks = blocks.predecessors();
            let mut suc_infos: HashMap<BasicBlock, Vec<BasicBlock>> = HashMap::new();
            for i in 0..=blocks.len() - 1 {
                suc_infos.insert(BasicBlock::from_usize(i), vec![]);
            }
            for (block, data) in blocks.iter_enumerated() {
                let statements = data.statements.clone();
                let terminator = data.terminator.clone().unwrap();
                let mut block_pre_blocks: Vec<BasicBlock> = vec![];
                for b in &pre_blocks[block] {
                    block_pre_blocks.push(*b);
                    suc_infos.get_mut(b).unwrap().push(block);
                }
                let a_block = MyBlock {
                    block_name: block,
                    statements,
                    terminator,
                    pre_blocks: block_pre_blocks,
                    suc_blocks: vec![],
                };
                fn_blocks.push(a_block);
            }
            for block in fn_blocks.iter_mut() {
                block.suc_blocks = suc_infos.get(&block.block_name).unwrap().clone();
            }
            let a_fn_block = FnBlocks {
                fn_name,
                fn_source,
                start_node: blocks.start_node(),
                blocks: fn_blocks,
                dominators: blocks.dominators().clone(),
                cond_chains: vec![],
                source_map: tcx.sess.source_map(),
                cond_map: cond_map.clone(),
            };
            ret.push(a_fn_block);
        }

        for mut block in ret {
            info!("Start analysis for {:?}", block.fn_name);
            block.mir_out();
            block.dump_cfg_to_dot();
            let result = block.iterative_dfs();
            if result {
                // info!("Dump condition chains to json");
                block.dump_to_json();
            }
        }
    }
}
