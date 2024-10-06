use super::branchvisitor::{ASTBranchVisitor, HIRBranchVisitor};
use crate::analysis::option::AnalysisOption;
use log::info;
use petgraph::dot::Config;
use petgraph::dot::Dot;
use petgraph::graph::DiGraph;
use petgraph::prelude::*;
use regex::Regex;
use rustc_ast::visit as astvisit;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_data_structures::graph::StartNode;
use rustc_driver::Compilation;
use rustc_hir::def;
use rustc_hir::intravisit as hirvisit;
use rustc_interface::interface;
use rustc_interface::Queries;
use rustc_middle::mir::BasicBlock;
use rustc_middle::mir::Statement;
use rustc_middle::mir::StatementKind;
use rustc_middle::mir::Terminator;
use rustc_middle::mir::TerminatorKind;
use rustc_middle::ty::TyCtxt;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;
use std::io::Write;

pub fn get_span_string(
    file_path: String,
    line_number: i32,
    start_column: i32,
    end_column: i32,
) -> String {
    // 读取指定文件
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);

    // 遍历文件每一行
    let specific_line = reader
        .lines()
        .enumerate()
        .filter_map(|(i, line)| {
            if i + 1 == line_number as usize {
                line.ok()
            } else {
                None
            }
        })
        .next()
        .unwrap_or_else(|| "".to_string());

    // 从特定行中提取列范围的文本
    let snippet = specific_line
        .chars()
        .skip((start_column - 1) as usize) // 跳过到起始列的字符
        .take((end_column - start_column) as usize) // 提取指定长度的字符
        .collect::<String>();

    println!("Extracted snippet: '{}'", snippet);
    snippet
}

pub struct MirCheckerCallbacks {
    pub analysis_options: AnalysisOption,
    pub source_name: String,
}

impl MirCheckerCallbacks {
    pub fn new(options: AnalysisOption) -> Self {
        Self {
            analysis_options: options,
            source_name: String::new(),
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

    fn after_crate_root_parsing<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        _queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let query_result = _queries.parse().unwrap();
        let krate = query_result.borrow().clone();
        // println!("AST\n{:#?}", krate);
        let mut visitor = ASTBranchVisitor::new();
        println!("AST Branch Visitor");
        astvisit::walk_crate::<ASTBranchVisitor>(&mut visitor, &krate);

        visitor.print_map();

        let dir_path = "./ast";
        let file_path = format!("{}/ast.txt", dir_path);
        fs::create_dir_all(dir_path).unwrap();
        let mut file = File::create(file_path).unwrap();
        file.write_all(format!("{:#?}", krate).as_bytes()).unwrap();

        Compilation::Continue
    }

    /// Called after analysis. Return value instructs the compiler whether to
    /// continue the compilation afterwards (defaults to `Compilation::Continue`)
    fn after_analysis<'compiler, 'tcx>(
        &mut self,
        compiler: &'compiler interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries
            .global_ctxt()
            .unwrap()
            .enter(|tcx| self.run_analysis(compiler, tcx));
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

fn find_second_last_index<T: PartialEq>(vec: &[T], target: T) -> Option<usize> {
    let mut count = 0;
    let len = vec.len();

    for i in (0..len).rev() {
        if vec[i] == target {
            count += 1;
            if count == 2 {
                return Some(i);
            }
        }
    }

    None
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

#[derive(Clone, Debug)]
struct FnBlocks<'a> {
    fn_name: String,
    start_node: BasicBlock,
    blocks: Vec<MyBlock<'a>>,
    dominators: Dominators<BasicBlock>,
    cond_chains: Vec<Vec<(String, String)>>,
}

impl FnBlocks<'_> {
    fn my_cout(&self) {
        println!("{:?}", self.fn_name);
        println!();
        for block in &self.blocks {
            println!("{:?}", block.block_name);
            let mut i = 0;
            for statement in &block.statements {
                println!("{}: {:?}", i, statement);
                println!("{:?}", statement.source_info.span);
                i = i + 1;
            }
            println!("terminator {:#?}", block.terminator);
            println!("preds {:?}", block.pre_blocks);
            println!("succs {:?}", block.suc_blocks);
            let span = format!("{:?}", block.terminator.source_info.span);
            println!("{}", span);
            let re = Regex::new(r"^(.*?):(\d+):(\d+): (\d+):(\d+)").unwrap();
            if let Some(caps) = re.captures(&span) {
                let file_path = caps.get(1).map_or("", |m| m.as_str());
                let start_line = caps.get(2).map_or("", |m| m.as_str());
                let start_column = caps.get(3).map_or("", |m| m.as_str());
                let end_line = caps.get(4).map_or("", |m| m.as_str());
                let end_column = caps.get(5).map_or("", |m| m.as_str());

                // println!("File path: {}", file_path);
                // println!("Start: line {}, column {}", start_line, start_column);
                // println!("End: line {}, column {}", end_line, end_column);
                get_span_string(
                    file_path.to_string(),
                    start_line.parse::<i32>().unwrap(),
                    start_column.parse::<i32>().unwrap(),
                    end_column.parse::<i32>().unwrap(),
                );
            } else {
                println!("No match found");
            }
            println!();
        }
    }

    fn cond_chain_cout(&mut self) {
        let mut init: Vec<(String, String)> = Vec::new();
        init.push(("break".to_string(), 0.to_string()));
        self.dfs(0, init);
        let mut i = 0;
        let mut file_string: String = String::new();
        for cond_chain in self.cond_chains.clone() {
            file_string = file_string + &format!("CondChain {}\n", i);
            println!("CondChain {}", i);
            let mut chain: String = "".to_string();
            let mut cfgflow: String = "".to_string();
            for (s1, s2) in cond_chain {
                if s1 != "break" {
                    if chain.len() == 0 {
                        chain = s1;
                    } else {
                        chain = chain + " -> " + s1.as_str();
                    }
                }
                if cfgflow.len() == 0 {
                    cfgflow = s2;
                } else {
                    cfgflow = cfgflow + " " + s2.as_str();
                }
            }
            file_string = file_string + &format!("{}\n", chain);
            file_string = file_string + &format!("{}\n", cfgflow);
            println!("{}", chain);
            println!("{}", cfgflow);
            println!();
            i = i + 1;
        }
        let dir_path = "./branch-info";
        let file_path = format!("{}/{}_condchain.txt", dir_path, self.fn_name);
        fs::create_dir_all(dir_path).unwrap();
        let mut file = File::create(file_path).unwrap();
        file.write_all(file_string.as_bytes()).unwrap();
    }

    fn dfs(&mut self, i: usize, cond_chain: Vec<(String, String)>) {
        if self.blocks[i].suc_blocks.len() == 0 {
            self.cond_chains.push(cond_chain.clone());
        } else if let Terminator {
            kind: TerminatorKind::SwitchInt { targets, .. },
            ..
        } = self.blocks[i].terminator.clone()
        {
            let mut string_kind = format!("{:?}", &self.blocks[i].terminator.kind);
            let mut start_index = string_kind.find('(').unwrap();
            let end_index = string_kind.find(')').unwrap();
            string_kind = string_kind[start_index + 1..end_index].to_string();
            start_index = string_kind.find('_').unwrap();
            let var = string_kind[start_index..].to_string();
            let terminator = self.blocks[i].terminator.clone();
            for (value, target) in targets.iter() {
                if !cond_chain
                    .iter()
                    .any(|pair| pair.1 == usize::from(target).to_string())
                {
                    let mut new_cond_chain = cond_chain.clone();
                    let span = format!("{:?}", terminator.source_info.span);
                    // println!("span: {}", span);
                    let re = Regex::new(r"^(.*?):(\d+):(\d+): (\d+):(\d+)").unwrap();
                    if let Some(caps) = re.captures(&span) {
                        let file_path = caps.get(1).map_or("", |m| m.as_str());
                        let start_line = caps.get(2).map_or("", |m| m.as_str());
                        let start_column = caps.get(3).map_or("", |m| m.as_str());
                        let end_line = caps.get(4).map_or("", |m| m.as_str());
                        let end_column = caps.get(5).map_or("", |m| m.as_str());

                        // println!("File path: {}", file_path);
                        // println!("Start: line {}, column {}", start_line, start_column);
                        // println!("End: line {}, column {}", end_line, end_column);
                        let cond = get_span_string(
                            file_path.to_string(),
                            start_line.parse::<i32>().unwrap(),
                            start_column.parse::<i32>().unwrap(),
                            end_column.parse::<i32>().unwrap(),
                        );
                        new_cond_chain.push((
                            format!("{} == {}", cond, value),
                            usize::from(target).to_string(),
                        ));
                        self.dfs(usize::from(target), new_cond_chain);
                    }
                } else {
                    let mut new_cond_chain = cond_chain.clone();
                    let span = format!("{:?}", terminator.source_info.span);
                    // println!("{}", span);
                    let re = Regex::new(r"^(.*?):(\d+):(\d+): (\d+):(\d+)").unwrap();
                    if let Some(caps) = re.captures(&span) {
                        let file_path = caps.get(1).map_or("", |m| m.as_str());
                        let start_line = caps.get(2).map_or("", |m| m.as_str());
                        let start_column = caps.get(3).map_or("", |m| m.as_str());
                        let end_line = caps.get(4).map_or("", |m| m.as_str());
                        let end_column = caps.get(5).map_or("", |m| m.as_str());

                        // println!("File path: {}", file_path);
                        // println!("Start: line {}, column {}", start_line, start_column);
                        // println!("End: line {}, column {}", end_line, end_column);
                        let cond = get_span_string(
                            file_path.to_string(),
                            start_line.parse::<i32>().unwrap(),
                            start_column.parse::<i32>().unwrap(),
                            end_column.parse::<i32>().unwrap(),
                        );
                        new_cond_chain.push((
                            format!("{} == {}", cond, value),
                            usize::from(target).to_string(),
                        ));
                        self.cond_chains.push(new_cond_chain.clone());
                    }
                }
            }
            if !cond_chain
                .iter()
                .any(|pair| pair.1 == usize::from(targets.otherwise()).to_string())
            {
                let mut new_cond_chain = cond_chain.clone();
                let span = format!("{:?}", terminator.source_info.span);
                // println!("{}", span);
                let re = Regex::new(r"^(.*?):(\d+):(\d+): (\d+):(\d+)").unwrap();
                if let Some(caps) = re.captures(&span) {
                    let file_path = caps.get(1).map_or("", |m| m.as_str());
                    let start_line = caps.get(2).map_or("", |m| m.as_str());
                    let start_column = caps.get(3).map_or("", |m| m.as_str());
                    let end_line = caps.get(4).map_or("", |m| m.as_str());
                    let end_column = caps.get(5).map_or("", |m| m.as_str());

                    // println!("File path: {}", file_path);
                    // println!("Start: line {}, column {}", start_line, start_column);
                    // println!("End: line {}, column {}", end_line, end_column);
                    let cond = get_span_string(
                        file_path.to_string(),
                        start_line.parse::<i32>().unwrap(),
                        start_column.parse::<i32>().unwrap(),
                        end_column.parse::<i32>().unwrap(),
                    );
                    new_cond_chain.push((
                        format!("{} == 1", cond),
                        usize::from(targets.otherwise()).to_string(),
                    ));
                    self.dfs(usize::from(targets.otherwise()), new_cond_chain);
                }
            } else {
                let mut new_cond_chain = cond_chain.clone();
                let span = format!("{:?}", terminator.source_info.span);
                // println!("{}", span);
                let re = Regex::new(r"^(.*?):(\d+):(\d+): (\d+):(\d+)").unwrap();
                if let Some(caps) = re.captures(&span) {
                    let file_path = caps.get(1).map_or("", |m| m.as_str());
                    let start_line = caps.get(2).map_or("", |m| m.as_str());
                    let start_column = caps.get(3).map_or("", |m| m.as_str());
                    let end_line = caps.get(4).map_or("", |m| m.as_str());
                    let end_column = caps.get(5).map_or("", |m| m.as_str());

                    // println!("File path: {}", file_path);
                    // println!("Start: line {}, column {}", start_line, start_column);
                    // println!("End: line {}, column {}", end_line, end_column);
                    let cond = get_span_string(
                        file_path.to_string(),
                        start_line.parse::<i32>().unwrap(),
                        start_column.parse::<i32>().unwrap(),
                        end_column.parse::<i32>().unwrap(),
                    );
                    new_cond_chain.push((
                        format!("{} == 1", cond),
                        usize::from(targets.otherwise()).to_string(),
                    ));
                    self.cond_chains.push(new_cond_chain.clone());
                }
            }
        } else {
            // if !cond_chain
            //     .iter()
            //     .any(|pair| pair.1 == usize::from(self.blocks[i].suc_blocks[0]).to_string())
            // {
            let mut new_cond_chain = cond_chain.clone();
            new_cond_chain.push((
                "break".to_string(),
                usize::from(self.blocks[i].suc_blocks[0]).to_string(),
            ));
            self.dfs(usize::from(self.blocks[i].suc_blocks[0]), new_cond_chain);
            // } else {
            //     self.cond_chains.push(cond_chain.clone());
            // }
        }
    }

    fn iterative_dfs(&mut self) {
        println!("-----------iterative_dfs------------");
        let mut stack: Vec<DFSCxt> = Vec::new();
        let dfs_cxt = DFSCxt::new(
            self.start_node,
            vec![self.start_node],
            Vec::new(),
            HashSet::new(),
            Vec::new(),
        );
        stack.push(dfs_cxt);
        let re = Regex::new(r"^(.*?):(\d+):(\d+): (\d+):(\d+)").unwrap();
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
            // println!("Block: {:?}", block_index);
            // println!("Path: {:?}", path);
            // println!("Loop Path: {:?}", loop_paths);
            let block = &self.blocks[block_index];

            // Check if a loop path is duplicated
            let mut dup_loop = false;
            let mut path2 = path.clone();
            for loop_path in &loop_paths {
                let count = count_subsequence(&path2, loop_path);
                // println!("count: {:?}", count);
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
                // println!("Loop Path: {:?}", loop_path);
            }

            // extract the condition
            if block.suc_blocks.is_empty() {
                // continue;
                println!("Final Conds: {:?}", conds);
                println!("Final Path: {:?}", path);
            } else if let Terminator {
                kind: TerminatorKind::SwitchInt { targets, .. },
                source_info,
            } = block.terminator.clone()
            {
                for (value, target) in targets.iter() {
                    let mut path = path.clone();
                    let mut branches = branches.clone();
                    if branches.insert((block.block_name, target)) {
                        // new branch
                        let span_str = format!("{:?}", source_info.span);
                        if let Some(caps) = re.captures(&span_str) {
                            let file_path = caps.get(1).map_or("", |m| m.as_str());
                            let start_line = caps.get(2).map_or("", |m| m.as_str());
                            let start_column = caps.get(3).map_or("", |m| m.as_str());
                            let end_line = caps.get(4).map_or("", |m| m.as_str());
                            let end_column = caps.get(5).map_or("", |m| m.as_str());

                            let cond = get_span_string(
                                file_path.to_string(),
                                start_line.parse::<i32>().unwrap(),
                                start_column.parse::<i32>().unwrap(),
                                end_column.parse::<i32>().unwrap(),
                            );
                            let mut conds = conds.clone();
                            conds.push((cond, value.to_string()));

                            path.push(target);
                            stack.push(DFSCxt::new(
                                target,
                                path,
                                conds,
                                branches,
                                loop_paths.clone(),
                            ));
                        }
                    } else {
                    }
                }
                let mut path = path.clone();
                let mut branches = branches.clone();
                if branches.insert((block.block_name, targets.otherwise())) {
                    // new branch
                    let span_str = format!("{:?}", source_info.span);
                    if let Some(caps) = re.captures(&span_str) {
                        let file_path = caps.get(1).map_or("", |m| m.as_str());
                        let start_line = caps.get(2).map_or("", |m| m.as_str());
                        let start_column = caps.get(3).map_or("", |m| m.as_str());
                        let end_line = caps.get(4).map_or("", |m| m.as_str());
                        let end_column = caps.get(5).map_or("", |m| m.as_str());

                        let cond = get_span_string(
                            file_path.to_string(),
                            start_line.parse::<i32>().unwrap(),
                            start_column.parse::<i32>().unwrap(),
                            end_column.parse::<i32>().unwrap(),
                        );
                        let mut conds = conds.clone();
                        conds.push((cond, "otherwise".to_string()));

                        path.push(targets.otherwise());
                        stack.push(DFSCxt::new(
                            targets.otherwise(),
                            path,
                            conds,
                            branches,
                            loop_paths,
                        ));
                    }
                } else {
                }
            } else {
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
        println!("-----------iterative_dfs------------");
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
    fn run_analysis<'tcx, 'compiler>(
        &mut self,
        compiler: &'compiler interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) {
        let mut ret: Vec<FnBlocks> = vec![];
        let hir_krate = tcx.hir();
        for id in hir_krate.items() {
            let item = id.owner_id.def_id;
            match tcx.def_kind(item) {
                def::DefKind::Fn => {
                    //函数
                    let fn_name = format!("{:?}", item.to_def_id());
                    let mut fn_blocks: Vec<MyBlock> = vec![];
                    let mut mir = tcx.optimized_mir(item);
                    let hir = hir_krate.maybe_body_owned_by(item).unwrap();
                    // println!("HIR\n{:#?}", hir);
                    let mut visitor = HIRBranchVisitor { tcx };
                    println!("HIR Branch Visitor");
                    hirvisit::walk_body::<HIRBranchVisitor>(&mut visitor, &hir);

                    let dir_path = "./hir";
                    let file_path = format!("{}/hir.txt", dir_path);
                    fs::create_dir_all(dir_path).unwrap();
                    let mut file = File::create(file_path).unwrap();
                    file.write_all(format!("{:#?}", hir).as_bytes()).unwrap();

                    // println!("{:#?}", mir);
                    let mut mir2 = mir.clone();
                    let blocks = &mir.basic_blocks;
                    // println!("{:#?}", blocks.reverse_postorder());
                    // println!("{:#?}", blocks.predecessors());
                    let pre_blocks = blocks.predecessors();
                    let mut bblocks = mir2.basic_blocks.as_mut_preserves_cfg();
                    let mut suc_infos: HashMap<BasicBlock, Vec<BasicBlock>> = HashMap::new();
                    for i in 0..=blocks.len() - 1 {
                        suc_infos.insert(BasicBlock::from_usize(i), vec![]);
                    }
                    for (block, data) in bblocks.iter().enumerate() {
                        // println!("{:#?}", block);
                        // println!("{:#?}", blocks.reverse_postorder()[block]);
                        // println!("{:#?}", data);
                        let block_name = BasicBlock::from_usize(block);
                        // println!("{:#?}", blocks[block_name]);
                        // println!("{:#?}", block);
                        // println!("{:#?}", pre_blocks[block_name]);
                        let statements = data.statements.clone();
                        let terminator = data.terminator.clone().unwrap();
                        let mut block_pre_blocks: Vec<BasicBlock> = vec![];
                        for b in pre_blocks[block_name].clone() {
                            block_pre_blocks.push(b);
                            suc_infos.get_mut(&b).unwrap().push(block_name);
                        }
                        let mut block_suc_blocks: Vec<BasicBlock> = vec![];
                        let mut a_block = MyBlock {
                            block_name: block_name,
                            statements: statements,
                            terminator: terminator,
                            pre_blocks: block_pre_blocks,
                            suc_blocks: block_suc_blocks,
                        };
                        fn_blocks.push(a_block);
                        // println!("{:#?}", a_block.clone());
                    }
                    for block in &mut fn_blocks {
                        block.suc_blocks = suc_infos.get(&block.block_name).unwrap().clone();
                    }
                    // println!("{:#?}", fn_blocks);
                    let a_fn_block = FnBlocks {
                        fn_name: fn_name.clone(),
                        start_node: mir2.basic_blocks.start_node(),
                        blocks: fn_blocks.clone(),
                        dominators: mir2.basic_blocks.dominators().clone(),
                        cond_chains: Vec::new(),
                    };
                    ret.push(a_fn_block);

                    // println!("{}", fn_name.clone());
                    // println!("{:#?}", mir);
                    println!();
                }
                _ => {
                    // println!("mir other kind: {:?}", tcx.def_kind(item));
                }
            }
        }
        for mut block in ret {
            block.my_cout();
            block.dump_cfg_to_dot();
            block.iterative_dfs();
            block.cond_chain_cout();
        }
    }
}
