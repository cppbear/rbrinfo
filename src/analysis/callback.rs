use super::branchvisitor::BranchVisitor;
use super::condition::{Arm, BoolCond, Condition, PattKind};
use super::sourceinfo::SourceInfo;
use crate::analysis::option::AnalysisOption;
use log::info;
use petgraph::dot::Config;
use petgraph::dot::Dot;
use petgraph::graph::DiGraph;
use petgraph::prelude::*;
use regex::Regex;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_data_structures::graph::StartNode;
use rustc_driver::Compilation;
use rustc_hir::def;
use rustc_hir::intravisit as hirvisit;
use rustc_interface::interface;
use rustc_interface::Queries;
use rustc_middle::mir::BasicBlock;
use rustc_middle::mir::Statement;
use rustc_middle::mir::{Terminator, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use std::collections::{HashMap, HashSet};
use std::fs::{self, File};
use std::io::Write;

pub struct MirCheckerCallbacks {
    pub analysis_options: AnalysisOption,
    pub source_name: String,
    cond_map: HashMap<SourceInfo, Condition>,
}

impl MirCheckerCallbacks {
    pub fn new(options: AnalysisOption) -> Self {
        Self {
            analysis_options: options,
            source_name: String::new(),
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
    ) -> Option<(Condition, Option<SourceInfo>)> {
        if let Some(cond) = self.cond_map.get(source_info) {
            return Some((cond.clone(), None));
        }

        for (k, v) in &self.cond_map {
            if source_info.contains(k) || k.contains(source_info) {
                return Some((v.clone(), None));
            }
            if let Condition::Match(match_cond) = v {
                // FIXME: return a vec of matched pat_sources
                for (pat_source, _) in &match_cond.arms {
                    if source_info.contains(pat_source) || pat_source.contains(source_info) {
                        return Some((v.clone(), Some(pat_source.clone())));
                    }
                }
            }
        }

        None
    }

    fn block_in_arm(&self, block: &MyBlock, arm: &Arm) -> bool {
        for stmt in &block.statements {
            if arm
                .body_source
                .contains(&self.get_source_info(stmt.source_info.span))
            {
                return true;
            }
        }
        if arm
            .body_source
            .contains(&self.get_source_info(block.terminator.source_info.span))
        {
            return true;
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

    fn iterative_dfs(&mut self) {
        // println!("-----------iterative_dfs------------");
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
                        let cond_source = self.get_source_info(ter_source.span);
                        for (value, target) in targets.iter() {
                            let mut path = path.clone();
                            let mut branches = branches.clone();
                            if branches.insert((block.block_name, target)) {
                                // new branch
                                if let Some((condition, arm_source)) =
                                    self.get_matched_cond(&cond_source)
                                {
                                    let mut conds = conds.clone();
                                    match condition {
                                        Condition::Bool(bool_cond) => match bool_cond {
                                            BoolCond::Binary(bin_cond) => {
                                                if bin_cond.eq_with_int() {
                                                    conds.push((
                                                        bin_cond.get_cond_str(),
                                                        "true".to_string(),
                                                    ));
                                                } else if bin_cond.ne_with_int() {
                                                    conds.push((
                                                        bin_cond.get_cond_str(),
                                                        "false".to_string(),
                                                    ));
                                                } else {
                                                    if value == 0 {
                                                        conds.push((
                                                            bin_cond.get_cond_str(),
                                                            "false".to_string(),
                                                        ));
                                                    } else {
                                                        conds.push((
                                                            bin_cond.get_cond_str(),
                                                            "true".to_string(),
                                                        ));
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
                                            conds.push((
                                                for_cond.get_cond_str(),
                                                value_str.to_string(),
                                            ));
                                        }
                                        Condition::Match(match_cond) => {
                                            // match arm.pat.kind {
                                            //     PattKind::Enum(_) => {
                                            //         conds.push((
                                            //             match_cond.match_str.clone(),
                                            //             "true".to_string(),
                                            //         ));
                                            //     }
                                            //     PattKind::StructLike(_) => {
                                            //         conds.push((
                                            //             match_cond.match_str.clone(),
                                            //             "true".to_string(),
                                            //         ));
                                            //     }
                                            //     PattKind::Other(pat) => {
                                            //         if let Some(_) = pat {
                                            //             conds.push((
                                            //                 format!(
                                            //                     "{} matches {}",
                                            //                     match_cond.match_str,
                                            //                     arm.pat.pat_str
                                            //                 ),
                                            //                 "true".to_string(),
                                            //             ));
                                            //         } else {
                                            //             if value == 0 {
                                            //                 conds.push((
                                            //                     format!(
                                            //                         "{} matches {}",
                                            //                         match_cond.match_str,
                                            //                         arm.pat.pat_str
                                            //                     ),
                                            //                     "false".to_string(),
                                            //                 ));
                                            //             }
                                            //         }
                                            //     }
                                            // }
                                            if let Some(pat_source) = arm_source {
                                                let arm = match_cond.arms.get(&pat_source).unwrap();
                                                if self
                                                    .block_in_arm(&self.blocks[target.index()], arm)
                                                {
                                                    conds.push((
                                                        format!(
                                                            "{} matches {}",
                                                            match_cond.match_str, arm.pat.pat_str
                                                        ),
                                                        "true".to_string(),
                                                    ));
                                                } else {
                                                    conds.push((
                                                        format!(
                                                            "{} matches {}",
                                                            match_cond.match_str, arm.pat.pat_str
                                                        ),
                                                        "false".to_string(),
                                                    ));
                                                }
                                            } else {
                                                for (_, arm) in &match_cond.arms {
                                                    if self.block_in_arm(
                                                        &self.blocks[target.index()],
                                                        arm,
                                                    ) {
                                                        conds.push((
                                                            format!(
                                                                "{} matches {}",
                                                                match_cond.match_str,
                                                                arm.pat.pat_str
                                                            ),
                                                            "true".to_string(),
                                                        ));
                                                        break;
                                                    }
                                                }
                                            }
                                            // FIXME: need to handle the case when the arm body is empty, and locate the matched arm more accurately
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
                            if branches.insert((block.block_name, targets.otherwise())) {
                                // new branch
                                if let Some((condition, arm_source)) =
                                    self.get_matched_cond(&cond_source)
                                {
                                    let mut conds = conds.clone();
                                    match condition {
                                        Condition::Bool(bool_cond) => match bool_cond {
                                            BoolCond::Binary(bin_cond) => {
                                                if bin_cond.eq_with_int() {
                                                    conds.push((
                                                        bin_cond.get_cond_str(),
                                                        "false".to_string(),
                                                    ));
                                                } else if bin_cond.ne_with_int() {
                                                    conds.push((
                                                        bin_cond.get_cond_str(),
                                                        "true".to_string(),
                                                    ));
                                                } else {
                                                    conds.push((
                                                        bin_cond.get_cond_str(),
                                                        "true".to_string(),
                                                    ));
                                                }
                                            }
                                            BoolCond::Other(cond_str) => {
                                                conds.push((cond_str, "true".to_string()));
                                            }
                                        },
                                        Condition::For(for_cond) => {
                                            conds.push((
                                                for_cond.get_cond_str(),
                                                "otherwise".to_string(),
                                            ));
                                        }
                                        Condition::Match(match_cond) => {
                                            if let Some(pat_source) = arm_source {
                                                let arm = match_cond.arms.get(&pat_source).unwrap();
                                                if self.block_in_arm(
                                                    &self.blocks[targets.otherwise().index()],
                                                    arm,
                                                ) {
                                                    conds.push((
                                                        format!(
                                                            "{} matches {}",
                                                            match_cond.match_str, arm.pat.pat_str
                                                        ),
                                                        "true".to_string(),
                                                    ));
                                                } else {
                                                    conds.push((
                                                        format!(
                                                            "{} matches {}",
                                                            match_cond.match_str, arm.pat.pat_str
                                                        ),
                                                        "false".to_string(),
                                                    ));
                                                }
                                            } else {
                                                for (_, arm) in &match_cond.arms {
                                                    if self.block_in_arm(
                                                        &self.blocks[targets.otherwise().index()],
                                                        arm,
                                                    ) {
                                                        conds.push((
                                                            format!(
                                                                "{} matches {}",
                                                                match_cond.match_str,
                                                                arm.pat.pat_str
                                                            ),
                                                            "true".to_string(),
                                                        ));
                                                        break;
                                                    }
                                                }
                                            }
                                            // FIXME: need to handle the case when the arm body is empty, and locate the matched arm more accurately
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
                    TerminatorKind::FalseEdge {
                        real_target,
                        imaginary_target,
                    } => {
                        let cond_source = self.get_source_info(ter_source.span);
                        let mut path = path.clone();
                        // let branches = branches.clone();
                        let mut conds = conds.clone();
                        if let Some((condition, arm_source)) = self.get_matched_cond(&cond_source) {
                            match condition {
                                Condition::Match(match_cond) => {
                                    if let Some(pat_source) = arm_source {
                                        let arm = match_cond.arms.get(&pat_source).unwrap();
                                        conds.push((
                                            format!(
                                                "{} matches {}",
                                                match_cond.match_str, arm.pat.pat_str
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
        // println!("-----------iterative_dfs------------\n");
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
                    let mut visitor = BranchVisitor::new(tcx, tcx.typeck(hir.id().hir_id.owner));
                    hirvisit::walk_body::<BranchVisitor>(&mut visitor, &hir);
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
                        re: Regex::new(r"^(.*?):(\d+):(\d+): (\d+):(\d+)").unwrap(),
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
