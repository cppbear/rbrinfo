use super::condition::{Arm, BoolCond, Condition, MatchCond, MatchKind, PattKind};
use super::exporter::{BrData, Cond, CondChain, ModInfo};
use super::sourceinfo::SourceInfo;
use petgraph::dot::Config;
use petgraph::dot::Dot;
use petgraph::graph::DiGraph;
use petgraph::prelude::*;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::mir::{BasicBlock, Operand};
use rustc_middle::mir::{Const, ConstValue, Rvalue, Statement, StatementKind, SwitchTargets};
use rustc_middle::mir::{Terminator, TerminatorKind};
use rustc_span::source_map::SourceMap;
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use std::fs::{self, File};
use std::io::Write;

#[derive(Clone, Debug)]
pub struct MyBlock<'a> {
    pub block_name: BasicBlock,
    pub statements: Vec<Statement<'a>>,
    pub terminator: Terminator<'a>,
    pub pre_blocks: Vec<BasicBlock>,
    pub suc_blocks: Vec<BasicBlock>,
}

#[derive(Clone, Debug)]
struct DFSCxt {
    block: BasicBlock,
    path: Vec<BasicBlock>,
    conds: Vec<Cond>,
    branches: HashSet<(BasicBlock, BasicBlock)>,
    loop_paths: Vec<Vec<BasicBlock>>,
}

impl DFSCxt {
    fn new(
        block: BasicBlock,
        path: Vec<BasicBlock>,
        conds: Vec<Cond>,
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

fn get_codes(fn_source: &SourceInfo) -> Vec<String> {
    let code = fn_source.get_string();
    let lines: Vec<&str> = code.lines().collect();
    let mut codes = vec![];
    if let Some(first_line) = lines.first() {
        let leading_spaces = first_line.chars().take_while(|c| c.is_whitespace()).count()
            + fn_source.get_startcolumn()
            - 1;
        codes = lines
            .iter()
            .map(|line| {
                let line_leading_spaces = line.chars().take_while(|c| c.is_whitespace()).count();
                let spaces_to_trim = line_leading_spaces.min(leading_spaces);
                line.chars().skip(spaces_to_trim).collect::<String>()
            })
            .collect();
    }
    codes
}

#[derive(Clone)]
pub struct FnBlocks<'a> {
    pub id: String,
    pub name: String,
    has_ret: bool,
    fn_source: SourceInfo,
    start_node: BasicBlock,
    blocks: Vec<MyBlock<'a>>,
    dominators: Dominators<BasicBlock>,
    cond_chains: BrData,
    source_map: &'a SourceMap,
    cond_map: HashMap<SourceInfo, HashSet<Condition>>,
}

impl<'a> FnBlocks<'a> {
    const MAX_CONDITIONS: usize = 9999;

    pub fn new(
        id: String,
        name: String,
        doc: String,
        has_ret: bool,
        fn_source: SourceInfo,
        mod_info: ModInfo,
        visible: bool,
        start_node: BasicBlock,
        blocks: Vec<MyBlock<'a>>,
        dominators: Dominators<BasicBlock>,
        source_map: &'a SourceMap,
        cond_map: HashMap<SourceInfo, HashSet<Condition>>,
    ) -> Self {
        let codes = get_codes(&fn_source);
        Self {
            id,
            name: name.clone(),
            has_ret,
            fn_source: fn_source.clone(),
            start_node,
            blocks,
            dominators,
            cond_chains: BrData::new(name, mod_info, visible, fn_source, doc, codes),
            source_map,
            cond_map,
        }
    }

    fn get_source_info(&self, span: rustc_span::Span) -> SourceInfo {
        SourceInfo::from_span(span, self.source_map)
    }

    fn get_matched_cond(
        &self,
        source_info: &SourceInfo,
        path: &Vec<BasicBlock>,
    ) -> Option<(Condition, Option<Vec<SourceInfo>>)> {
        if let Some(cond) = self.cond_map.get(source_info) {
            if cond.len() == 1 {
                return Some((cond.iter().next().unwrap().clone(), None));
            } else {
                for bb in path.iter().rev() {
                    for c in cond {
                        if self.block_contains_cond(*bb, source_info) {
                            return Some((c.clone(), None));
                        }
                        if let Condition::Match(match_cond) = c {
                            if self.block_contains_cond(*bb, &match_cond.match_source) {
                                return Some((c.clone(), None));
                            }
                        }
                    }
                }
                return None;
            }
        }

        for (k, v) in &self.cond_map {
            if source_info.contains(k) || k.contains(source_info) {
                if v.len() == 1 {
                    return Some((v.iter().next().unwrap().clone(), None));
                } else {
                    for bb in path.iter().rev() {
                        for c in v {
                            if self.block_contains_cond(*bb, k) {
                                return Some((c.clone(), None));
                            }
                            if let Condition::Match(match_cond) = c {
                                if self.block_contains_cond(*bb, &match_cond.match_source) {
                                    return Some((c.clone(), None));
                                }
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

    pub fn mir_out(&self) {
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
        let dir_path = format!("./rbrinfo/{}", self.id);
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
            warn!("Span of Terminator for Enum points to an arm pattern, this is NOT common. Check {:?}", block_name);
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
                        PattKind::Enum(_) => {
                            if value == 0 {
                                conds.push(Cond::new(
                                    format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                    "false".to_string(),
                                    pat_sources[0].get_startline(),
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
                        conds.push(Cond::new(
                            format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                            "true".to_string(),
                            pat_sources[0].get_startline(),
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
                    let mut pat_strs = vec![];
                    for (arm_source, arm) in &match_cond.arms {
                        match arm.pat.kind {
                            PattKind::Enum(index) => {
                                if value == index as u128 {
                                    pat_strs.push(arm.pat.pat_str.clone());
                                    found = true;
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
                    conds.push(Cond::new(
                        format!("{} matches {}", match_cond.match_str, pat_strs.join(" or ")),
                        "true".to_string(),
                        match_cond.match_source.get_startline(),
                    ));
                    if !found {
                        if matches!(
                            self.blocks[target.index()].terminator.kind,
                            TerminatorKind::FalseEdge { .. }
                        ) {
                            warn!(
                            "No matched arm found for Enum {}, branch {:?} -> {:?} (Terminator is FalseEdge)",
                            value, block_name, target
                        );
                        } else {
                            error!(
                            "No matched arm found for Enum {}, branch {:?} -> {:?}, condition {:?}",
                            value, block_name, target, match_cond
                        );
                        }
                        // Check if the target block is in the arm body
                        for (arm_source, arm) in &match_cond.arms {
                            if self.block_in_arm(&self.blocks[target.index()], arm) {
                                conds.push(Cond::new(
                                    format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                    "true".to_string(),
                                    arm_source.get_startline(),
                                ));
                                info!("The target block is in the arm body");
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
                            conds.push(Cond::new(
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "false".to_string(),
                                arm_source.get_startline(),
                            ));
                            found = true;
                        }
                        PattKind::Wild => {
                            conds.push(Cond::new(
                                format!("{} matches _", match_cond.match_str),
                                "true".to_string(),
                                arm_source.get_startline(),
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
                    for (arm_source, arm) in &match_cond.arms {
                        if self.block_in_arm(&self.blocks[targets.otherwise().index()], arm) {
                            conds.push(Cond::new(
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "true".to_string(),
                                arm_source.get_startline(),
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
                                        conds.push(Cond::new(
                                            format!(
                                                "{}.{} matches {}",
                                                match_cond.match_str,
                                                match_cond.match_kind.get_field_name(*field_index),
                                                field_source.get_string()
                                            ),
                                            "true".to_string(),
                                            field_source.get_startline(),
                                        ));
                                    } else {
                                        if value != 0 {
                                            error!("Value not equal to 0");
                                        }
                                        conds.push(Cond::new(
                                            format!(
                                                "{}.{} matches {}",
                                                match_cond.match_str,
                                                match_cond.match_kind.get_field_name(*field_index),
                                                field_source.get_string()
                                            ),
                                            "false".to_string(),
                                            field_source.get_startline(),
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
                                                    conds.push(Cond::new(
                                                        format!(
                                                            "{}.{} matches {}",
                                                            match_cond.match_str,
                                                            match_cond
                                                                .match_kind
                                                                .get_field_name(idx.index()),
                                                            field_source.get_string()
                                                        ),
                                                        "true".to_string(),
                                                        field_source.get_startline(),
                                                    ));
                                                } else {
                                                    if value != 0 {
                                                        error!("Value not equal to 0");
                                                    }
                                                    conds.push(Cond::new(
                                                        format!(
                                                            "{}.{} matches {}",
                                                            match_cond.match_str,
                                                            match_cond
                                                                .match_kind
                                                                .get_field_name(idx.index()),
                                                            field_source.get_string()
                                                        ),
                                                        "false".to_string(),
                                                        field_source.get_startline(),
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
                                conds.push(Cond::new(
                                    format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                    "true".to_string(),
                                    pat_sources[0].get_startline(),
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
                                    conds.push(Cond::new(
                                        format!(
                                            "{}.{} matches {}",
                                            match_cond.match_str,
                                            match_cond.match_kind.get_field_name(*field_index),
                                            field_source.get_string()
                                        ),
                                        "false".to_string(),
                                        field_source.get_startline(),
                                    ));
                                } else {
                                    conds.push(Cond::new(
                                        format!(
                                            "{}.{} matches {}",
                                            match_cond.match_str,
                                            match_cond.match_kind.get_field_name(*field_index),
                                            field_source.get_string()
                                        ),
                                        "true".to_string(),
                                        field_source.get_startline(),
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
                                                    conds.push(Cond::new(
                                                        format!(
                                                            "{}.{} matches {}",
                                                            match_cond.match_str,
                                                            match_cond
                                                                .match_kind
                                                                .get_field_name(idx.index()),
                                                            source.get_string()
                                                        ),
                                                        "false".to_string(),
                                                        source.get_startline(),
                                                    ));
                                                } else {
                                                    conds.push(Cond::new(
                                                        format!(
                                                            "{}.{} matches {}",
                                                            match_cond.match_str,
                                                            match_cond
                                                                .match_kind
                                                                .get_field_name(idx.index()),
                                                            source.get_string()
                                                        ),
                                                        "true".to_string(),
                                                        source.get_startline(),
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
                            conds.push(Cond::new(
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "true".to_string(),
                                pat_sources[0].get_startline(),
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
                                                        conds.push(Cond::new(
                                                            format!(
                                                                "{}.{} matches {}",
                                                                match_cond.match_str,
                                                                match_cond
                                                                    .match_kind
                                                                    .get_field_name(idx.index()),
                                                                source.get_string()
                                                            ),
                                                            "true".to_string(),
                                                            cond_source.get_startline(),
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
                    for (arm_source, arm) in &match_cond.arms {
                        if self.block_in_arm(&self.blocks[target.index()], arm) {
                            conds.push(Cond::new(
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "true".to_string(),
                                arm_source.get_startline(),
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
                                                    conds.push(Cond::new(
                                                        format!(
                                                            "{}.{} matches {}",
                                                            match_cond.match_str,
                                                            match_cond
                                                                .match_kind
                                                                .get_field_name(idx.index()),
                                                            source.get_string()
                                                        ),
                                                        "true".to_string(),
                                                        cond_source.get_startline(),
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
                for (arm_source, arm) in &match_cond.arms {
                    if self.block_in_arm(&self.blocks[targets.otherwise().index()], arm) {
                        conds.push(Cond::new(
                            format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                            "true".to_string(),
                            arm_source.get_startline(),
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
                                conds.push(Cond::new(
                                    format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                    "true".to_string(),
                                    pat_sources[0].get_startline(),
                                ));
                            } else {
                                if value != 0 {
                                    error!("Value not equal to 0");
                                }
                                conds.push(Cond::new(
                                    format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                    "false".to_string(),
                                    pat_sources[0].get_startline(),
                                ));
                            }
                            // Check if the target block is in the arm body
                            if self.block_in_arm(&self.blocks[target.index()], arm) {
                                conds.push(Cond::new(
                                    format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                    "true".to_string(),
                                    pat_sources[0].get_startline(),
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
                            conds.push(Cond::new(
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "false".to_string(),
                                pat_sources[0].get_startline(),
                            ));
                        } else {
                            conds.push(Cond::new(
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "true".to_string(),
                                pat_sources[0].get_startline(),
                            ));
                        }
                        // Check if the target block is in the arm body
                        if self.block_in_arm(&self.blocks[targets.otherwise().index()], arm) {
                            conds.push(Cond::new(
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "true".to_string(),
                                pat_sources[0].get_startline(),
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
                                        conds.push(Cond::new(
                                            format!(
                                                "{} matches {}",
                                                match_cond.match_str, arm.pat.pat_str
                                            ),
                                            "true".to_string(),
                                            arm_source.get_startline(),
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
                    for (arm_source, arm) in &match_cond.arms {
                        if self.block_in_arm(&self.blocks[target.index()], arm) {
                            conds.push(Cond::new(
                                format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                                "true".to_string(),
                                arm_source.get_startline(),
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
                                    conds.push(Cond::new(
                                        format!(
                                            "{} matches {}",
                                            match_cond.match_str, arm.pat.pat_str
                                        ),
                                        "true".to_string(),
                                        arm_source.get_startline(),
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
                for (arm_source, arm) in &match_cond.arms {
                    if self.block_in_arm(&self.blocks[targets.otherwise().index()], arm) {
                        conds.push(Cond::new(
                            format!("{} matches {}", match_cond.match_str, arm.pat.pat_str),
                            "true".to_string(),
                            arm_source.get_startline(),
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

    fn try_get_const(&self, op: &Operand<'a>, path: &Vec<BasicBlock>) -> Option<u128> {
        if let Some(constop) = op.constant() {
            if let Const::Val(ConstValue::Scalar(Scalar::Int(sint)), _) = constop.const_ {
                let value = sint.to_bits(sint.size());
                return Some(value);
            }
        }
        if let Some(place) = op.place() {
            'outer: for bb in path.iter().rev() {
                let block = &self.blocks[bb.index()];
                for stmt in block.statements.iter().rev() {
                    if let StatementKind::Assign(assign) = &stmt.kind {
                        if place == assign.0 {
                            if let Rvalue::Use(Operand::Constant(constop)) = &assign.1 {
                                if let Const::Val(ConstValue::Scalar(Scalar::Int(sint)), _) =
                                    constop.const_
                                {
                                    let value = sint.to_bits(sint.size());
                                    return Some(value);
                                }
                            }
                            break 'outer;
                        }
                    }
                }
            }
        }
        None
    }

    fn handle_switchint(
        &self,
        stack: &mut Vec<DFSCxt>,
        dfs_cxt: &DFSCxt,
        ternimator_span: Span,
        discr: &Operand<'a>,
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
        // Determine whether `discr` is a constant
        let value = self.try_get_const(discr, path);
        if let Some(constv) = value {
            info!("Operand of SwitchInt is a constant: {:?}", constv);
            let mut found = false;
            // common branches
            for (value, target) in targets.iter() {
                if value == constv {
                    found = true;
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
                    break;
                }
            }
            // otherwise branch
            if !found {
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
            return;
        }

        let cond_source = self.get_source_info(ternimator_span);
        if let Some((condition, arm_source)) = self.get_matched_cond(&cond_source, path) {
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
                                    let mut cond = Cond::new(
                                        bin_cond.get_cond_str(),
                                        "true".to_string(),
                                        cond_source.get_startline(),
                                    );
                                    cond.bound = bin_cond.get_bound(true);
                                    cond.norm = bin_cond.get_norm_str();
                                    conds.push(cond);
                                } else if bin_cond.ne_with_int() {
                                    let mut cond = Cond::new(
                                        bin_cond.get_cond_str(),
                                        "false".to_string(),
                                        cond_source.get_startline(),
                                    );
                                    cond.bound = bin_cond.get_bound(false);
                                    cond.norm = bin_cond.get_norm_str();
                                    conds.push(cond);
                                } else {
                                    if value == 0 {
                                        let mut cond = Cond::new(
                                            bin_cond.get_cond_str(),
                                            "false".to_string(),
                                            cond_source.get_startline(),
                                        );
                                        cond.bound = bin_cond.get_bound(false);
                                        cond.norm = bin_cond.get_norm_str();
                                        conds.push(cond);
                                    } else {
                                        let mut cond = Cond::new(
                                            bin_cond.get_cond_str(),
                                            "true".to_string(),
                                            cond_source.get_startline(),
                                        );
                                        cond.bound = bin_cond.get_bound(true);
                                        cond.norm = bin_cond.get_norm_str();
                                        conds.push(cond);
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
                                let mut cond = Cond::new(
                                    bin_cond.get_cond_str(),
                                    "false".to_string(),
                                    cond_source.get_startline(),
                                );
                                cond.bound = bin_cond.get_bound(false);
                                cond.norm = bin_cond.get_norm_str();
                                conds.push(cond);
                            } else if bin_cond.ne_with_int() {
                                let mut cond = Cond::new(
                                    bin_cond.get_cond_str(),
                                    "true".to_string(),
                                    cond_source.get_startline(),
                                );
                                cond.bound = bin_cond.get_bound(true);
                                cond.norm = bin_cond.get_norm_str();
                                conds.push(cond);
                            } else {
                                let mut cond = Cond::new(
                                    bin_cond.get_cond_str(),
                                    "true".to_string(),
                                    cond_source.get_startline(),
                                );
                                cond.bound = bin_cond.get_bound(true);
                                cond.norm = bin_cond.get_norm_str();
                                conds.push(cond);
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
                                    conds.push(Cond::new(
                                        cond_str.clone(),
                                        "false".to_string(),
                                        cond_source.get_startline(),
                                    ));
                                } else {
                                    conds.push(Cond::new(
                                        cond_str.clone(),
                                        "true".to_string(),
                                        cond_source.get_startline(),
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
                        let mut branches = branches.clone();
                        if !matches!(
                            self.blocks[targets.otherwise().index()].terminator.kind,
                            TerminatorKind::Unreachable
                        ) && branches.insert((block_name, targets.otherwise()))
                        {
                            let mut path = path.clone();
                            let mut conds = conds.clone();

                            conds.push(Cond::new(
                                cond_str.clone(),
                                "true".to_string(),
                                cond_source.get_startline(),
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
                            conds.push(Cond::new(
                                for_cond.get_cond_str(),
                                value_str.to_string(),
                                cond_source.get_startline(),
                            ));

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

                        conds.push(Cond::new(
                            for_cond.get_cond_str(),
                            "otherwise".to_string(),
                            cond_source.get_startline(),
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
                            conds.push(Cond::new(
                                try_str.clone(),
                                value_str.to_string(),
                                cond_source.get_startline(),
                            ));

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

                        conds.push(Cond::new(
                            try_str.clone(),
                            "otherwise".to_string(),
                            cond_source.get_startline(),
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
            }
        } else {
            warn!(
                "No matched condition found for {:?} in {:?}",
                cond_source, block_name
            );
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

    fn get_ret(&self, path: &Vec<BasicBlock>) -> Option<String> {
        if self.has_ret {
            for bb in path.iter().rev() {
                let block = &self.blocks[bb.index()];
                for stmt in block.statements.iter().rev() {
                    if let StatementKind::Assign(assign) = &stmt.kind {
                        let place = assign.0;
                        if place.local.index() == 0 {
                            let ret_source = self.get_source_info(stmt.source_info.span);
                            return Some(ret_source.get_string());
                        }
                    }
                }
            }
        }
        None
    }

    pub fn iterative_dfs(&mut self) -> bool {
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
                let ret_value = self.get_ret(path);
                let mut chain = CondChain::new(
                    conds.clone(),
                    path.iter().map(|x| x.index()).collect::<Vec<usize>>(),
                    ret_value,
                );
                chain.set_may_contra();
                self.cond_chains.add_chain(chain);
                if self.cond_chains.chain_len() > Self::MAX_CONDITIONS {
                    warn!("Too many condition chains");
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
                            self.get_matched_cond(&cond_source, &path)
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
                                            .join(" or ");
                                        conds.push(Cond::new(
                                            format!(
                                                "{} matches {}",
                                                match_cond.match_str, pat_strs
                                            ),
                                            "true".to_string(),
                                            match_cond.match_source.get_startline(),
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
        self.cond_chains.set_min_set();
        self.cond_chains.set_size();

        true
    }

    pub fn dump_to_json(&self) {
        let dir_path = "./rbrinfo/brdata";
        let file_path = format!("{}/{}.json", dir_path, self.id);
        fs::create_dir_all(dir_path).unwrap();
        let json = serde_json::to_string_pretty(&self.cond_chains).unwrap();
        let mut file = File::create(file_path).unwrap();
        file.write_all(json.as_bytes()).unwrap();
    }

    pub fn dump_cfg_to_dot(&self) {
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
        let mut file = File::create(format!("rbrinfo/{}/cfg.dot", self.id)).unwrap();
        writeln!(file, "{:#}", dot).unwrap();
    }
}
