use super::branchvisitor::BranchVisitor;
use super::condition::{Arm, BoolCond, Condition, MatchCond, MatchKind, PattKind};
use super::option::AnalysisOption;
use super::sourceinfo::SourceInfo;
use petgraph::dot::Config;
use petgraph::dot::Dot;
use petgraph::graph::DiGraph;
use petgraph::prelude::*;
use regex::Regex;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_data_structures::graph::StartNode;
use rustc_driver::Compilation;
use rustc_hir::def;
use rustc_hir::intravisit;
use rustc_interface::interface;
use rustc_interface::Queries;
use rustc_middle::mir::{BasicBlock, Operand};
use rustc_middle::mir::{Statement, SwitchTargets};
use rustc_middle::mir::{Terminator, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use simplelog::{ColorChoice, ConfigBuilder, LevelFilter, TermLogger, TerminalMode};
use std::collections::{HashMap, HashSet};
use std::fs::{self, File};
use std::io::Write;
use time::UtcOffset;

pub struct MirCheckerCallbacks {
    pub analysis_options: AnalysisOption,
    pub source_name: String,
    span_re: Regex,
    cond_map: HashMap<SourceInfo, Condition>,
}

impl MirCheckerCallbacks {
    pub fn new(options: AnalysisOption) -> Self {
        Self {
            analysis_options: options,
            source_name: String::new(),
            span_re: Regex::new(r"^(.*?):(\d+):(\d+): (\d+):(\d+)").unwrap(),
            cond_map: HashMap::new(),
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

// fn find_second_last_index<T: PartialEq>(vec: &[T], target: T) -> Option<usize> {
//     let mut count = 0;
//     let len = vec.len();

//     for i in (0..len).rev() {
//         if vec[i] == target {
//             count += 1;
//             if count == 2 {
//                 return Some(i);
//             }
//         }
//     }

//     None
// }

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

#[derive(Clone, Debug)]
struct FnBlocks<'a> {
    fn_name: String,
    start_node: BasicBlock,
    blocks: Vec<MyBlock<'a>>,
    dominators: Dominators<BasicBlock>,
    cond_chains: Vec<Vec<(String, String)>>,
    re: Regex,
    cond_map: HashMap<SourceInfo, Condition>,
}

impl FnBlocks<'_> {
    fn get_source_info(&self, span: rustc_span::Span) -> SourceInfo {
        SourceInfo::from_span(span, &self.re)
    }

    fn get_matched_cond(
        &self,
        source_info: &SourceInfo,
    ) -> Option<(Condition, Option<Vec<SourceInfo>>)> {
        if let Some(cond) = self.cond_map.get(source_info) {
            return Some((cond.clone(), None));
        }

        for (k, v) in &self.cond_map {
            if source_info.contains(k) || k.contains(source_info) {
                return Some((v.clone(), None));
            }
            if let Condition::Match(match_cond) = v {
                let mut sources = vec![];
                for (pat_source, _) in &match_cond.arms {
                    if source_info.contains(pat_source) || pat_source.contains(source_info) {
                        // Terminator of kind falseEdge may contain multiple patterns
                        sources.push(pat_source.clone());
                    }
                }
                if !sources.is_empty() {
                    return Some((v.clone(), Some(sources)));
                }
            }
        }

        None
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
        mir_str.push_str(&format!("fn {}\n\n", self.fn_name));
        for block in &self.blocks {
            mir_str.push_str(&format!("{:?}\n", block.block_name));
            let mut i = 0;
            for statement in &block.statements {
                mir_str.push_str(&format!("  {}: {:?}\n", i, statement));
                mir_str.push_str(&format!("    {:?}\n", statement.source_info.span));
                i = i + 1;
            }
            let formatted = format!("{:#?}\n", block.terminator);
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
        let dir_path = "./mir";
        let file_path = format!("{}/mir.txt", dir_path);
        fs::create_dir_all(dir_path).unwrap();
        let mut file = File::create(file_path).unwrap();
        file.write_all(mir_str.as_bytes()).unwrap();
    }

    fn handle_switchint(
        &self,
        discr: &Operand,
        targets: &SwitchTargets,
        block_name: BasicBlock,
        ternimator_span: Span,
        path: &Vec<BasicBlock>,
        branches: &HashSet<(BasicBlock, BasicBlock)>,
        conds: &Vec<(String, String)>,
        stack: &mut Vec<DFSCxt>,
        loop_paths: &Vec<Vec<BasicBlock>>,
    ) {
        let cond_source = self.get_source_info(ternimator_span);
        let cmp_value = if targets.iter().len() == 1 {
            Some(targets.iter().next().unwrap().0)
        } else {
            None
        };
        for (value, target) in targets.iter() {
            let mut path = path.clone();
            let mut branches = branches.clone();
            if branches.insert((block_name, target)) {
                // new branch
                if let Some((condition, arm_source)) = self.get_matched_cond(&cond_source) {
                    let mut conds = conds.clone();
                    match condition {
                        Condition::Bool(bool_cond) => match bool_cond {
                            BoolCond::Binary(bin_cond) => {
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
                            }
                            BoolCond::Other(cond_str) => {
                                if value == 0 {
                                    conds.push((cond_str, "false".to_string()));
                                } else {
                                    conds.push((cond_str, "true".to_string()));
                                }
                            }
                        },
                        Condition::For(for_cond) => {
                            let value_str = match value {
                                0 => "false",
                                1 => "true",
                                _ => panic!("Invalid value"),
                            };
                            conds.push((for_cond.get_cond_str(), value_str.to_string()));
                        }
                        Condition::Match(match_cond) => {
                            let mut found = false;
                            if let Some(pat_sources) = arm_source {
                                assert_eq!(pat_sources.len(), 1);
                                let pat_source = &pat_sources[0];
                                let arm = match_cond.arms.get(pat_source).unwrap();
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
                                                found = true;
                                            }
                                        } else {
                                            if value == 0 {
                                                conds.push((
                                                    format!(
                                                        "{} matches {}",
                                                        match_cond.match_str, arm.pat.pat_str
                                                    ),
                                                    "false".to_string(),
                                                ));
                                                found = true;
                                            }
                                        }
                                    }
                                    PattKind::Enum(index) => {
                                        if value == *index as u128 {
                                            conds.push((
                                                format!(
                                                    "{} matches {}",
                                                    match_cond.match_str, arm.pat.pat_str
                                                ),
                                                "true".to_string(),
                                            ));
                                            found = true;
                                        }
                                    }
                                    PattKind::StructLike(field_map) => {
                                        for (field_index, (lit, source)) in field_map {
                                            if cond_source == *source {
                                                info!("Ternimator span points to field pattern");
                                                if let Some(lit) = lit {
                                                    if value == *lit {
                                                        conds.push((
                                                            format!(
                                                                "{}.{} matches {}",
                                                                match_cond.match_str,
                                                                match_cond
                                                                    .match_kind
                                                                    .get_field_name(*field_index),
                                                                source.get_string()
                                                            ),
                                                            "true".to_string(),
                                                        ));
                                                    }
                                                } else {
                                                    if value == 0 {
                                                        conds.push((
                                                            format!(
                                                                "{}.{} matches {}",
                                                                match_cond.match_str,
                                                                match_cond
                                                                    .match_kind
                                                                    .get_field_name(*field_index),
                                                                source.get_string()
                                                            ),
                                                            "false".to_string(),
                                                        ));
                                                    }
                                                }
                                                found = true;
                                                break;
                                            }
                                        }
                                        if !found {
                                            warn!("UNCOMMON");
                                            match discr {
                                                Operand::Copy(place) | Operand::Move(place) => {
                                                    println!(
                                                        "place: {:?} {:?}",
                                                        place, place.projection
                                                    );
                                                    for proj in place.projection.iter() {
                                                        if let rustc_middle::mir::ProjectionElem::Field(
                                                                                idx,
                                                                                _,
                                                                            ) = proj
                                                                            {
                                                                                if let Some((lit, source)) =
                                                                                    field_map.get(&idx.index())
                                                                                {
                                                                                    if cond_source == *source {
                                                                                        if let Some(lit) = lit {
                                                                                            if value == *lit {
                                                                                                conds.push((
                                                                                                    format!(
                                                                                                        "{}.{} matches {}",
                                                                                                        match_cond.match_str,
                                                                                                        match_cond.match_kind.get_field_name(idx.index()),
                                                                                                        source.get_string()
                                                                                                    ),
                                                                                                    "true".to_string(),
                                                                                                ));
                                                                                            }
                                                                                        } else {
                                                                                            if value == 0 {
                                                                                                conds.push((
                                                                                                    format!(
                                                                                                        "{}.{} matches {}",
                                                                                                        match_cond.match_str,
                                                                                                        match_cond.match_kind.get_field_name(idx.index()),
                                                                                                        source.get_string()
                                                                                                    ),
                                                                                                    "false".to_string(),
                                                                                                ));
                                                                                            }
                                                                                        }
                                                                                        found = true;
                                                                                        break;
                                                                                    }
                                                                                }
                                                                            }
                                                    }
                                                }
                                                _ => {}
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                                if self.block_in_arm(&self.blocks[target.index()], arm) {
                                    conds.push((
                                        format!(
                                            "{} matches {}",
                                            match_cond.match_str, arm.pat.pat_str
                                        ),
                                        "true".to_string(),
                                    ));
                                    found = true;
                                }
                            }
                            if !found {
                                // println!("!found");
                                for (_, arm) in &match_cond.arms {
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
                                                    conds.push((
                                                        format!(
                                                            "{} matches {}",
                                                            match_cond.match_str, arm.pat.pat_str
                                                        ),
                                                        "false".to_string(),
                                                    ));
                                                    break;
                                                }
                                            }
                                        }
                                        PattKind::Enum(index) => {
                                            if value == *index as u128 {
                                                conds.push((
                                                    format!(
                                                        "{} matches {}",
                                                        match_cond.match_str, arm.pat.pat_str
                                                    ),
                                                    "true".to_string(),
                                                ));
                                                break;
                                            }
                                        }
                                        PattKind::StructLike(field_map) => {
                                            match discr {
                                                Operand::Copy(place) | Operand::Move(place) => {
                                                    // println!(
                                                    //     "place: {:?} {:?}",
                                                    //     place, place.projection
                                                    // );
                                                    for proj in place.projection.iter() {
                                                        if let rustc_middle::mir::ProjectionElem::Field(
                                                                                idx,
                                                                                _,
                                                                            ) = proj
                                                                            {
                                                                                if let Some((lit, source)) =
                                                                                    field_map.get(&idx.index())
                                                                                {
                                                                                    if let Some(lit) = lit {
                                                                                        if value == *lit {
                                                                                            conds.push((
                                                                                                format!(
                                                                                                    "{}.{} matches {}",
                                                                                                    match_cond.match_str,
                                                                                                    match_cond.match_kind.get_field_name(idx.index()),
                                                                                                    source.get_string()
                                                                                                ),
                                                                                                "true".to_string(),
                                                                                            ));
                                                                                            break;
                                                                                        }
                                                                                    }
                                                                                }
                                                                            }
                                                    }
                                                }
                                                _ => {}
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                            }
                            for (_, arm) in &match_cond.arms {
                                if self.block_in_arm(&self.blocks[target.index()], arm) {
                                    conds.push((
                                        format!(
                                            "{} matches {}",
                                            match_cond.match_str, arm.pat.pat_str
                                        ),
                                        "true".to_string(),
                                    ));
                                    break;
                                }
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
                } else {
                    panic!("No matched condition found for {:?}", cond_source);
                }
            } else {
            }
        }
        let mut path = path.clone();
        let mut branches = branches.clone();
        if !matches!(
            self.blocks[targets.otherwise().index()].terminator.kind,
            TerminatorKind::Unreachable
        ) {
            if branches.insert((block_name, targets.otherwise())) {
                // new branch
                if let Some((condition, arm_source)) = self.get_matched_cond(&cond_source) {
                    let mut conds = conds.clone();
                    match condition {
                        Condition::Bool(bool_cond) => match bool_cond {
                            BoolCond::Binary(bin_cond) => {
                                if bin_cond.eq_with_int() {
                                    conds.push((bin_cond.get_cond_str(), "false".to_string()));
                                } else if bin_cond.ne_with_int() {
                                    conds.push((bin_cond.get_cond_str(), "true".to_string()));
                                } else {
                                    conds.push((bin_cond.get_cond_str(), "true".to_string()));
                                }
                            }
                            BoolCond::Other(cond_str) => {
                                conds.push((cond_str, "true".to_string()));
                            }
                        },
                        Condition::For(for_cond) => {
                            conds.push((for_cond.get_cond_str(), "otherwise".to_string()));
                        }
                        Condition::Match(match_cond) => {
                            let mut found = false;
                            if let Some(pat_sources) = arm_source {
                                assert_eq!(pat_sources.len(), 1);
                                let pat_source = &pat_sources[0];
                                let arm = match_cond.arms.get(pat_source).unwrap();
                                match &arm.pat.kind {
                                    PattKind::Other(lit) => {
                                        if let Some(_) = lit {
                                            conds.push((
                                                format!(
                                                    "{} matches {}",
                                                    match_cond.match_str, arm.pat.pat_str
                                                ),
                                                "false".to_string(),
                                            ));
                                            found = true;
                                        } else {
                                            conds.push((
                                                format!(
                                                    "{} matches {}",
                                                    match_cond.match_str, arm.pat.pat_str
                                                ),
                                                "true".to_string(),
                                            ));
                                            found = true;
                                        }
                                    }
                                    PattKind::Enum(_) => {
                                        conds.push((
                                            format!(
                                                "{} matches {}",
                                                match_cond.match_str, arm.pat.pat_str
                                            ),
                                            "false".to_string(),
                                        ));
                                        found = true;
                                    }
                                    PattKind::StructLike(field_map) => {
                                        for (field_index, (lit, source)) in field_map {
                                            if cond_source == *source {
                                                if let Some(_) = lit {
                                                    conds.push((
                                                        format!(
                                                            "{}.{} matches {}",
                                                            match_cond.match_str,
                                                            match_cond
                                                                .match_kind
                                                                .get_field_name(*field_index),
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
                                                                .get_field_name(*field_index),
                                                            source.get_string()
                                                        ),
                                                        "true".to_string(),
                                                    ));
                                                }
                                                found = true;
                                                break;
                                            }
                                        }
                                        if !found {
                                            match discr {
                                                Operand::Copy(place) | Operand::Move(place) => {
                                                    // println!(
                                                    //     "place: {:?} {:?}",
                                                    //     place, place.projection
                                                    // );
                                                    for proj in place.projection.iter() {
                                                        if let rustc_middle::mir::ProjectionElem::Field(
                                                                                idx,
                                                                                _,
                                                                            ) = proj
                                                                            {
                                                                                if let Some((lit, source)) =
                                                                                    field_map.get(&idx.index())
                                                                                {
                                                                                    if cond_source == *source {
                                                                                        if let Some(_) = lit {
                                                                                            conds.push((
                                                                                                format!(
                                                                                                    "{}.{} matches {}",
                                                                                                    match_cond.match_str,
                                                                                                    match_cond.match_kind.get_field_name(idx.index()),
                                                                                                    source.get_string()
                                                                                                ),
                                                                                                "false".to_string(),
                                                                                            ));
                                                                                        } else {
                                                                                            conds.push((
                                                                                                format!(
                                                                                                    "{}.{} matches {}",
                                                                                                    match_cond.match_str,
                                                                                                    match_cond.match_kind.get_field_name(idx.index()),
                                                                                                    source.get_string()
                                                                                                ),
                                                                                                "true".to_string(),
                                                                                            ));
                                                                                        }
                                                                                        found = true;
                                                                                        break;
                                                                                    }
                                                                                }
                                                                            }
                                                    }
                                                }
                                                _ => {}
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                                if self.block_in_arm(&self.blocks[targets.otherwise().index()], arm)
                                {
                                    conds.push((
                                        format!(
                                            "{} matches {}",
                                            match_cond.match_str, arm.pat.pat_str
                                        ),
                                        "true".to_string(),
                                    ));
                                    found = true;
                                }
                            }
                            if !found {
                                // println!("otherwise !found");
                                for (_, arm) in &match_cond.arms {
                                    match &arm.pat.kind {
                                        PattKind::Other(lit) => {
                                            if let Some(lit) = lit {
                                                if let Some(cmp_value) = cmp_value {
                                                    if cmp_value == *lit {
                                                        conds.push((
                                                            format!(
                                                                "{} matches {}",
                                                                match_cond.match_str,
                                                                arm.pat.pat_str
                                                            ),
                                                            "false".to_string(),
                                                        ));
                                                        break;
                                                    }
                                                }
                                            }
                                        }
                                        PattKind::Enum(_) => {
                                            conds.push((
                                                format!(
                                                    "{} matches {}",
                                                    match_cond.match_str, arm.pat.pat_str
                                                ),
                                                "false".to_string(),
                                            ));
                                            // break;
                                        }
                                        PattKind::StructLike(field_map) => {
                                            match discr {
                                                Operand::Copy(place) | Operand::Move(place) => {
                                                    // println!(
                                                    //     "place: {:?} {:?}",
                                                    //     place, place.projection
                                                    // );
                                                    for proj in place.projection.iter() {
                                                        if let rustc_middle::mir::ProjectionElem::Field(
                                                                                idx,
                                                                                _,
                                                                            ) = proj
                                                                        {
                                                                            if let Some((lit, source)) =
                                                                                field_map.get(&idx.index())
                                                                            {
                                                                                if let Some(lit) = lit {
                                                                                    if let Some(cmp_value) = cmp_value {
                                                                                        if cmp_value == *lit {
                                                                                            conds.push((
                                                                                                format!(
                                                                                                    "{}.{} matches {}",
                                                                                                    match_cond.match_str,
                                                                                                    match_cond.match_kind.get_field_name(idx.index()),
                                                                                                    source.get_string()
                                                                                                ),
                                                                                                "false".to_string(),
                                                                                            ));
                                                                                            break;
                                                                                        }
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                    }
                                                }
                                                _ => {}
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                            }
                            for (_, arm) in &match_cond.arms {
                                if self.block_in_arm(&self.blocks[targets.otherwise().index()], arm)
                                {
                                    conds.push((
                                        format!(
                                            "{} matches {}",
                                            match_cond.match_str, arm.pat.pat_str
                                        ),
                                        "true".to_string(),
                                    ));
                                    break;
                                }
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
                } else {
                    panic!("No matched condition found");
                }
            } else {
            }
        }
    }

    fn handle_enum_match(
        &self,
        stack: &mut Vec<DFSCxt>,
        block_name: BasicBlock,
        path: &Vec<BasicBlock>,
        conds: &Vec<(String, String)>,
        branches: &HashSet<(BasicBlock, BasicBlock)>,
        loop_paths: &Vec<Vec<BasicBlock>>,

        targets: &SwitchTargets,
        match_cond: &MatchCond,
        arm_source: &Option<Vec<SourceInfo>>,
    ) {
        if let Some(pat_sources) = arm_source {
            // Span of Terminator points to a arm pattern
            error!("Span of Terminator for Enum points to an arm pattern, this is NOT common.");
            assert_eq!(pat_sources.len(), 1);
            let arm = match_cond.arms.get(&pat_sources[0]).unwrap();
            match arm.pat.kind {
                PattKind::Enum(index) => {
                    // common branches
                    for (value, target) in targets.iter() {
                        let mut path = path.clone();
                        let mut conds = conds.clone();
                        let mut branches = branches.clone();
                        if branches.insert((block_name, target)) {
                            // new branch
                            if value == index as u128 {
                                conds.push((
                                    format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                    "true".to_string(),
                                ));
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
                    let mut path = path.clone();
                    let mut conds = conds.clone();
                    let mut branches = branches.clone();
                    if !matches!(
                        self.blocks[targets.otherwise().index()].terminator.kind,
                        TerminatorKind::Unreachable
                    ) && branches.insert((block_name, targets.otherwise()))
                    {
                        // new branch
                        conds.push((
                            format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                            "false".to_string(),
                        ));
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
                PattKind::Wild => {
                    error!("Span of Terminator points to _ pattern");
                }
                _ => {
                    panic!("Invalid pattern kind for Enum");
                }
            }
        } else {
            // Span of Terminator does NOT point to a arm pattern, just "match XXX"
            info!("Span of Terminator does NOT point to a arm pattern");
            // TODO:
        }
    }

    fn handle_structlike_match(
        &self,
        stack: &mut Vec<DFSCxt>,
        block_name: BasicBlock,
        path: &mut Vec<BasicBlock>,
        conds: &mut Vec<(String, String)>,
        branches: &mut HashSet<(BasicBlock, BasicBlock)>,
        loop_paths: &Vec<Vec<BasicBlock>>,

        cond_source: &SourceInfo,
        discr: &Operand,
        targets: &SwitchTargets,
        match_cond: &MatchCond,
        arm_source: &Option<Vec<SourceInfo>>,
    ) {
        if let Some(pat_sources) = arm_source {
            // Span of Terminator points to a arm pattern
            info!("Span of Terminator points to a arm pattern");
            assert_eq!(pat_sources.len(), 1);
            let arm = match_cond.arms.get(&pat_sources[0]).unwrap();
            match &arm.pat.kind {
                PattKind::StructLike(field_map) => {
                    // common branches
                    let succ_size = targets.iter().len() + 1;
                    assert!(succ_size <= 2);
                    for (value, target) in targets.iter() {
                        if branches.insert((block_name, target)) {
                            // new branch
                            let mut found = true;
                            for (field_index, (lit, field_source)) in field_map {
                                if cond_source == field_source {
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
                            // TODO: push path and stack
                        }
                    }
                    // otherwise branch
                    if !matches!(
                        self.blocks[targets.otherwise().index()].terminator.kind,
                        TerminatorKind::Unreachable
                    ) && branches.insert((block_name, targets.otherwise()))
                    {
                        // new branch
                        let mut found = true;
                        for (field_index, (lit, field_source)) in field_map {
                            if cond_source == field_source {
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
                        // TODO: push path and stack
                    }
                }
                PattKind::Wild => {
                    error!("Span of Terminator points to _ pattern");
                }
                _ => {
                    panic!("Invalid pattern kind for Enum");
                }
            }
        } else {
            // Span of Terminator does NOT point to a arm pattern, just "match XXX"
            info!("Span of Terminator does NOT point to a arm pattern");
            // TODO:
        }
    }

    fn handle_other_match(
        &self,
        stack: &mut Vec<DFSCxt>,
        block_name: BasicBlock,
        path: &mut Vec<BasicBlock>,
        conds: &mut Vec<(String, String)>,
        branches: &mut HashSet<(BasicBlock, BasicBlock)>,
        loop_paths: &Vec<Vec<BasicBlock>>,

        targets: &SwitchTargets,
        match_cond: &MatchCond,
        arm_source: &Option<Vec<SourceInfo>>,
    ) {
        if let Some(pat_sources) = arm_source {
            // Span of Terminator points to a arm pattern
            info!("Span of Terminator points to a arm pattern");
            assert_eq!(pat_sources.len(), 1);
            let arm = match_cond.arms.get(&pat_sources[0]).unwrap();
            match arm.pat.kind {
                PattKind::Other(lit) => {
                    // common branches
                    for (value, target) in targets.iter() {
                        if branches.insert((block_name, target)) {
                            // new branch
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
                            if self.block_in_arm(&self.blocks[target.index()], arm) {
                                conds.push((
                                    format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                    "true".to_string(),
                                ));
                            }
                            // TODO: push path and stack
                        }
                    }
                    // otherwise branch
                    if !matches!(
                        self.blocks[targets.otherwise().index()].terminator.kind,
                        TerminatorKind::Unreachable
                    ) && branches.insert((block_name, targets.otherwise()))
                    {
                        // new branch
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
                        if self.block_in_arm(&self.blocks[targets.otherwise().index()], arm) {
                            conds.push((
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "true".to_string(),
                            ));
                        }
                        // TODO: push path and stack
                    }
                }
                PattKind::Wild => {
                    error!("Span of Terminator points to _ pattern");
                }
                _ => {
                    panic!("Invalid pattern kind for Enum");
                }
            }
        } else {
            // Span of Terminator does NOT point to a arm pattern, just "match XXX"
            info!("Span of Terminator does NOT point to a arm pattern");
            // TODO:
        }
    }

    fn handle_switchint_alt(
        &self,
        stack: &mut Vec<DFSCxt>,
        block_name: BasicBlock,
        path: &Vec<BasicBlock>,
        conds: &Vec<(String, String)>,
        branches: &HashSet<(BasicBlock, BasicBlock)>,
        loop_paths: &Vec<Vec<BasicBlock>>,

        ternimator_span: Span,
        discr: &Operand,
        targets: &SwitchTargets,
    ) {
        let cond_source = self.get_source_info(ternimator_span);
        if let Some((condition, arm_source)) = self.get_matched_cond(&cond_source) {
            let mut conds = conds.clone();
            let mut path = path.clone();
            let mut branches = branches.clone();
            match condition {
                Condition::Bool(bool_cond) => match bool_cond {
                    BoolCond::Binary(bin_cond) => {
                        // common branches
                        for (value, target) in targets.iter() {
                            if branches.insert((block_name, target)) {
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
                            }
                        }
                        // otherwise branch
                        if !matches!(
                            self.blocks[targets.otherwise().index()].terminator.kind,
                            TerminatorKind::Unreachable
                        ) && branches.insert((block_name, targets.otherwise()))
                        {
                            if bin_cond.eq_with_int() {
                                conds.push((bin_cond.get_cond_str(), "false".to_string()));
                            } else if bin_cond.ne_with_int() {
                                conds.push((bin_cond.get_cond_str(), "true".to_string()));
                            } else {
                                conds.push((bin_cond.get_cond_str(), "true".to_string()));
                            }
                        }
                    }
                    BoolCond::Other(cond_str) => {
                        // common branches
                        for (value, target) in targets.iter() {
                            if branches.insert((block_name, target)) {
                                if value == 0 {
                                    conds.push((cond_str.clone(), "false".to_string()));
                                } else {
                                    conds.push((cond_str.clone(), "true".to_string()));
                                }
                            }
                        }
                        // otherwise branch
                        if !matches!(
                            self.blocks[targets.otherwise().index()].terminator.kind,
                            TerminatorKind::Unreachable
                        ) && branches.insert((block_name, targets.otherwise()))
                        {
                            conds.push((cond_str, "true".to_string()));
                        }
                    }
                },
                Condition::For(for_cond) => {
                    // common branches
                    for (value, target) in targets.iter() {
                        if branches.insert((block_name, target)) {
                            let value_str = match value {
                                0 => "false",
                                1 => "true",
                                _ => panic!("Invalid value"),
                            };
                            conds.push((for_cond.get_cond_str(), value_str.to_string()));
                        }
                    }
                    // otherwise branch
                    if !matches!(
                        self.blocks[targets.otherwise().index()].terminator.kind,
                        TerminatorKind::Unreachable
                    ) && branches.insert((block_name, targets.otherwise()))
                    {
                        conds.push((for_cond.get_cond_str(), "otherwise".to_string()));
                    }
                }
                Condition::Match(match_cond) => {
                    let cmp_value = if targets.iter().len() == 1 {
                        Some(targets.iter().next().unwrap().0)
                    } else {
                        None
                    };
                    match &match_cond.match_kind {
                        MatchKind::Enum(_) => {
                            self.handle_enum_match(
                                stack,
                                block_name,
                                &path,
                                &conds,
                                &branches,
                                loop_paths,
                                targets,
                                &match_cond,
                                &arm_source,
                            );
                        }
                        MatchKind::StructLike(_) => {
                            self.handle_structlike_match(
                                stack,
                                block_name,
                                &mut path,
                                &mut conds,
                                &mut branches,
                                loop_paths,
                                &cond_source,
                                discr,
                                targets,
                                &match_cond,
                                &arm_source,
                            );
                        }
                        MatchKind::Other => {
                            self.handle_other_match(
                                stack,
                                block_name,
                                &mut path,
                                &mut conds,
                                &mut branches,
                                loop_paths,
                                targets,
                                &match_cond,
                                &arm_source,
                            );
                        }
                    }
                }
            }
        } else {
            panic!("No matched condition found for {:?}", cond_source);
        }

        //
        let cmp_value = if targets.iter().len() == 1 {
            Some(targets.iter().next().unwrap().0)
        } else {
            None
        };
        for (value, target) in targets.iter() {
            let mut path = path.clone();
            let mut branches = branches.clone();
            if branches.insert((block_name, target)) {
                // new branch
                if let Some((condition, arm_source)) = self.get_matched_cond(&cond_source) {
                    let mut conds = conds.clone();
                    match condition {
                        Condition::Match(match_cond) => {
                            let mut found = false;
                            if let Some(pat_sources) = arm_source {}
                            if !found {
                                println!("!found");
                                for (_, arm) in &match_cond.arms {
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
                                                    conds.push((
                                                        format!(
                                                            "{} matches {}",
                                                            match_cond.match_str, arm.pat.pat_str
                                                        ),
                                                        "false".to_string(),
                                                    ));
                                                    break;
                                                }
                                            }
                                        }
                                        PattKind::Enum(index) => {
                                            if value == *index as u128 {
                                                conds.push((
                                                    format!(
                                                        "{} matches {}",
                                                        match_cond.match_str, arm.pat.pat_str
                                                    ),
                                                    "true".to_string(),
                                                ));
                                                break;
                                            }
                                        }
                                        PattKind::StructLike(field_map) => {
                                            match discr {
                                                Operand::Copy(place) | Operand::Move(place) => {
                                                    // println!(
                                                    //     "place: {:?} {:?}",
                                                    //     place, place.projection
                                                    // );
                                                    for proj in place.projection.iter() {
                                                        if let rustc_middle::mir::ProjectionElem::Field(
                                                                                idx,
                                                                                _,
                                                                            ) = proj
                                                                            {
                                                                                if let Some((lit, source)) =
                                                                                    field_map.get(&idx.index())
                                                                                {
                                                                                    if let Some(lit) = lit {
                                                                                        if value == *lit {
                                                                                            conds.push((
                                                                                                format!(
                                                                                                    "{}.{} matches {}",
                                                                                                    match_cond.match_str,
                                                                                                    match_cond.match_kind.get_field_name(idx.index()),
                                                                                                    source.get_string()
                                                                                                ),
                                                                                                "true".to_string(),
                                                                                            ));
                                                                                            break;
                                                                                        }
                                                                                    }
                                                                                }
                                                                            }
                                                    }
                                                }
                                                _ => {}
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                            }
                            for (_, arm) in &match_cond.arms {
                                if self.block_in_arm(&self.blocks[target.index()], arm) {
                                    conds.push((
                                        format!(
                                            "{} matches {}",
                                            match_cond.match_str, arm.pat.pat_str
                                        ),
                                        "true".to_string(),
                                    ));
                                    break;
                                }
                            }
                        }
                        _ => {}
                    }
                    path.push(target);
                    stack.push(DFSCxt::new(
                        target,
                        path,
                        conds,
                        branches,
                        loop_paths.clone(),
                    ));
                } else {
                    panic!("No matched condition found for {:?}", cond_source);
                }
            }
        }
        let mut path = path.clone();
        let mut branches = branches.clone();
        if !matches!(
            self.blocks[targets.otherwise().index()].terminator.kind,
            TerminatorKind::Unreachable
        ) {
            if branches.insert((block_name, targets.otherwise())) {
                // new branch
                if let Some((condition, arm_source)) = self.get_matched_cond(&cond_source) {
                    let mut conds = conds.clone();
                    match condition {
                        Condition::Match(match_cond) => {
                            let mut found = false;
                            if let Some(pat_sources) = arm_source {}
                            if !found {
                                println!("otherwise !found");
                                for (_, arm) in &match_cond.arms {
                                    match &arm.pat.kind {
                                        PattKind::Other(lit) => {
                                            if let Some(lit) = lit {
                                                if let Some(cmp_value) = cmp_value {
                                                    if cmp_value == *lit {
                                                        conds.push((
                                                            format!(
                                                                "{} matches {}",
                                                                match_cond.match_str,
                                                                arm.pat.pat_str
                                                            ),
                                                            "false".to_string(),
                                                        ));
                                                        break;
                                                    }
                                                }
                                            }
                                        }
                                        PattKind::Enum(_) => {
                                            conds.push((
                                                format!(
                                                    "{} matches {}",
                                                    match_cond.match_str, arm.pat.pat_str
                                                ),
                                                "false".to_string(),
                                            ));
                                            // break;
                                        }
                                        PattKind::StructLike(field_map) => {
                                            match discr {
                                                Operand::Copy(place) | Operand::Move(place) => {
                                                    // println!(
                                                    //     "place: {:?} {:?}",
                                                    //     place, place.projection
                                                    // );
                                                    for proj in place.projection.iter() {
                                                        if let rustc_middle::mir::ProjectionElem::Field(
                                                                                idx,
                                                                                _,
                                                                            ) = proj
                                                                        {
                                                                            if let Some((lit, source)) =
                                                                                field_map.get(&idx.index())
                                                                            {
                                                                                if let Some(lit) = lit {
                                                                                    if let Some(cmp_value) = cmp_value {
                                                                                        if cmp_value == *lit {
                                                                                            conds.push((
                                                                                                format!(
                                                                                                    "{}.{} matches {}",
                                                                                                    match_cond.match_str,
                                                                                                    match_cond.match_kind.get_field_name(idx.index()),
                                                                                                    source.get_string()
                                                                                                ),
                                                                                                "false".to_string(),
                                                                                            ));
                                                                                            break;
                                                                                        }
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                    }
                                                }
                                                _ => {}
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                            }
                            for (_, arm) in &match_cond.arms {
                                if self.block_in_arm(&self.blocks[targets.otherwise().index()], arm)
                                {
                                    conds.push((
                                        format!(
                                            "{} matches {}",
                                            match_cond.match_str, arm.pat.pat_str
                                        ),
                                        "true".to_string(),
                                    ));
                                    break;
                                }
                            }
                        }
                        _ => {}
                    }
                    path.push(targets.otherwise());
                    stack.push(DFSCxt::new(
                        targets.otherwise(),
                        path,
                        conds,
                        branches,
                        loop_paths.clone(),
                    ));
                } else {
                    panic!("No matched condition found");
                }
            }
        }
    }

    fn iterative_dfs(&mut self) {
        let mut stack: Vec<DFSCxt> = Vec::new();
        let dfs_cxt = DFSCxt::new(
            self.start_node,
            vec![self.start_node],
            Vec::new(),
            HashSet::new(),
            Vec::new(),
        );
        stack.push(dfs_cxt);
        let mut cond_chains: Vec<(Vec<(String, String)>, Vec<BasicBlock>)> = Vec::new();
        while !stack.is_empty() {
            let dfs_cxt = stack.pop().unwrap();
            let DFSCxt {
                block,
                path,
                conds,
                branches,
                mut loop_paths,
            } = dfs_cxt;
            let block_index = block.index();

            let block = &self.blocks[block_index];

            // Check if a loop path is duplicated
            let mut dup_loop = false;
            let mut path2 = path.clone();
            for loop_path in &loop_paths {
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
                // continue;
                // println!("Final Conds: {:?}", conds);
                // println!("Final Path: {:?}", path);
                cond_chains.push((conds, path));
            } else {
                let ter_source = block.terminator.source_info;
                match &block.terminator.kind {
                    TerminatorKind::SwitchInt { discr, targets } => {
                        self.handle_switchint(
                            discr,
                            targets,
                            block.block_name,
                            ter_source.span,
                            &path,
                            &branches,
                            &conds,
                            &mut stack,
                            &loop_paths,
                        );
                    }
                    TerminatorKind::FalseEdge { real_target, .. } => {
                        let cond_source = self.get_source_info(ter_source.span);
                        let mut path = path.clone();
                        // let branches = branches.clone();
                        let mut conds = conds.clone();
                        if let Some((condition, arm_sources)) = self.get_matched_cond(&cond_source)
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
                            branches,
                            loop_paths.clone(),
                        ));
                    }
                    _ => {
                        let mut path = path.clone();
                        path.push(block.suc_blocks[0]);
                        stack.push(DFSCxt::new(
                            block.suc_blocks[0],
                            path,
                            conds,
                            branches,
                            loop_paths,
                        ));
                    }
                }
            }
        }
        let mut chain_id = 0;
        let mut chains_str = String::new();
        for (conds, path) in &cond_chains {
            chains_str += &format!("CondChain {}\n", chain_id);
            let mut cond_iter = 0;
            for (cond, value) in conds {
                if cond_iter == 0 {
                    chains_str += &format!("{} is {}", cond, value);
                } else {
                    chains_str += &format!(" -> {} is {}", cond, value);
                }
                cond_iter += 1;
            }
            chains_str += "\n";
            let mut path_iter = 0;
            for block in path {
                if path_iter == 0 {
                    chains_str += &format!("{:?}", block);
                } else {
                    chains_str += &format!(" -> {:?}", block);
                }
                path_iter += 1;
            }
            chains_str += "\n";
            if chain_id != cond_chains.len() - 1 {
                chains_str += "\n";
            }
            chain_id += 1;
        }
        println!("{}", chains_str);
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
        let mut file = File::create(format!("{}_cfg.dot", self.fn_name)).unwrap();
        writeln!(file, "{:#}", dot).unwrap();
    }
}

impl MirCheckerCallbacks {
    fn run_analysis<'tcx, 'compiler>(&mut self, tcx: TyCtxt<'tcx>) {
        let time_offset = UtcOffset::from_hms(8, 0, 0).unwrap(); // Set time zone to UTC+8
        let log_config = ConfigBuilder::new()
            .set_location_level(LevelFilter::Info)
            .set_time_offset(time_offset)
            .build();
        TermLogger::init(
            LevelFilter::Info,
            log_config,
            TerminalMode::Mixed,
            ColorChoice::Auto,
        )
        .unwrap();
        info!("Start analysis");
        let mut ret: Vec<FnBlocks> = vec![];
        let hir_krate = tcx.hir();
        for id in hir_krate.items() {
            let item = id.owner_id.def_id;
            match tcx.def_kind(item) {
                def::DefKind::Fn => {
                    //函数
                    let fn_name = format!("{:?}", item.to_def_id());
                    let hir = hir_krate.body_owned_by(item);
                    let mir = tcx.mir_built(item).borrow();
                    // write HIR to file
                    let dir_path = "./hir";
                    let file_path = format!("{}/hir.txt", dir_path);
                    fs::create_dir_all(dir_path).unwrap();
                    let mut file = File::create(file_path).unwrap();
                    let buf = format!("{}\n\n{:#?}", fn_name, hir);
                    file.write_all(buf.as_bytes()).unwrap();
                    // tranverse HIR
                    let fn_source = SourceInfo::from_span(hir.value.span, &self.span_re);
                    let mut visitor = BranchVisitor::new(
                        tcx,
                        fn_source,
                        self.span_re.clone(),
                        tcx.typeck(hir.id().hir_id.owner),
                    );
                    intravisit::walk_body::<BranchVisitor>(&mut visitor, &hir);
                    // visitor.walk_body
                    visitor.output_map();
                    self.cond_map = visitor.move_map();

                    let mut fn_blocks: Vec<MyBlock> = vec![];
                    let blocks = &mir.basic_blocks;
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
                        start_node: blocks.start_node(),
                        blocks: fn_blocks,
                        dominators: blocks.dominators().clone(),
                        cond_chains: vec![],
                        re: self.span_re.clone(),
                        cond_map: self.cond_map.clone(),
                    };
                    ret.push(a_fn_block);
                }
                _ => {
                    // println!("mir other kind: {:?}", tcx.def_kind(item));
                }
            }
        }
        for mut block in ret {
            block.mir_out();
            block.dump_cfg_to_dot();
            block.iterative_dfs();
        }
    }
}
