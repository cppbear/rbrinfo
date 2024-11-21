use rustc_span::sym::sub;

use super::sourceinfo::SourceInfo;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, serde::Serialize)]
pub struct BrData {
    name: String,
    mod_info: ModInfo,
    loc: SourceInfo,
    codes: Vec<String>,
    cond_chains: Vec<CondChain>,
}

impl BrData {
    pub fn new(name: String, mod_info: ModInfo, loc: SourceInfo, codes: Vec<String>) -> Self {
        Self {
            name,
            mod_info,
            loc,
            codes,
            cond_chains: vec![],
        }
    }

    pub fn chain_len(&self) -> usize {
        self.cond_chains.len()
    }

    pub fn add_chain(&mut self, mut chain: CondChain) {
        chain.id = self.cond_chains.len() + 1;
        self.cond_chains.push(chain);
    }

    pub fn set_min_set(&mut self) {
        let mut uncovered: HashSet<_> = self
            .cond_chains
            .iter()
            .flat_map(|chain| chain.get_cond_set())
            .collect();
        let (non_contra, contra): (Vec<_>, Vec<_>) =
            self.cond_chains.iter_mut().partition(|s| !s.may_contra);
        for subset in [non_contra, contra].iter_mut() {
            while !uncovered.is_empty() {
                if let Some(best) = subset
                    .iter_mut()
                    .filter(|s| !s.get_cond_set().is_disjoint(&uncovered))
                    .max_by_key(|s| s.get_cond_set().intersection(&uncovered).count())
                {
                    best.min_set = true;
                    uncovered = uncovered
                        .difference(&best.get_cond_set())
                        .cloned()
                        .collect();
                } else {
                    break;
                }
            }
        }
    }
}

#[derive(Debug, Clone, serde::Serialize)]
pub struct ModInfo {
    pub name: String,
    pub loc: SourceInfo,
}

#[derive(Debug, Clone, serde::Serialize)]
pub struct CondChain {
    id: usize,
    conds: Vec<Cond>,
    ret: Option<String>,
    path: Vec<usize>,
    may_contra: bool,
    min_set: bool,
}

impl CondChain {
    pub fn new(conds: Vec<Cond>, path: Vec<usize>, ret: Option<String>) -> Self {
        Self {
            id: 0,
            conds,
            path,
            ret,
            may_contra: false,
            min_set: false,
        }
    }

    pub fn get_cond_set(&self) -> HashSet<(usize, String, String)> {
        self.conds
            .iter()
            .map(|c| {
                (
                    c.line,
                    c.norm.clone().unwrap_or(c.cond.clone()),
                    c.value.clone(),
                )
            })
            .collect()
    }

    pub fn set_may_contra(&mut self) {
        let mut map = HashMap::new();
        for cond in &self.conds {
            if let Some(flag) = map.get(cond.norm.as_ref().unwrap_or(&cond.cond)) {
                if flag != &cond.value {
                    self.may_contra = true;
                    break;
                }
            } else {
                map.insert(
                    cond.norm.clone().unwrap_or(cond.cond.clone()),
                    cond.value.clone(),
                );
            }
        }
    }
}

#[derive(Debug, Clone, serde::Serialize)]
pub struct Cond {
    pub cond: String,
    pub norm: Option<String>,
    pub value: String,
    pub line: usize,
    pub bound: Option<String>,
}

impl Cond {
    pub fn new(cond: String, value: String, line: usize) -> Self {
        Self {
            cond,
            norm: None,
            value,
            line,
            bound: None,
        }
    }
}
