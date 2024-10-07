use std::collections::BTreeMap;

use super::branchvisitor::SourceInfo;

#[derive(Clone, Debug)]
pub enum Condition {
    Bool(BoolCond),
    For(ForCond),
    Match(MatchCond),
}

#[derive(Clone, Debug)]
pub enum CmpIntKind {
    No,
    Eq,
    Ne,
}

#[derive(Clone, Debug)]
pub struct BoolCond {
    cond_str: String,
    cmp_with_int: CmpIntKind,
}

impl BoolCond {
    pub fn new(cond_str: String, cmp_with_int: CmpIntKind) -> Self {
        Self {
            cond_str,
            cmp_with_int,
        }
    }

    pub fn eq_with_int(&self) -> bool {
        match self.cmp_with_int {
            CmpIntKind::Eq => true,
            _ => false,
        }
    }

    pub fn ne_with_int(&self) -> bool {
        match self.cmp_with_int {
            CmpIntKind::Ne => true,
            _ => false,
        }
    }

    pub fn get_cond_str(&self) -> &str {
        &self.cond_str
    }
}

#[derive(Clone, Debug)]
pub struct ForCond {
    iter_var: String,
    iter_range: String,
}

impl ForCond {
    pub fn new(iter_var: String, iter_range: String) -> Self {
        Self {
            iter_var,
            iter_range,
        }
    }

    pub fn get_iter_var(&self) -> &str {
        &self.iter_var
    }

    pub fn get_iter_range(&self) -> &str {
        &self.iter_range
    }

    pub fn get_cond_str(&self) -> String {
        format!("{} in {}", self.iter_var, self.iter_range)
    }
}

#[derive(Clone, Debug)]
pub struct Arm {
    pat: String,
    body_source: Option<SourceInfo>,
}

impl Arm {
    pub fn new(pat: String, body_source: Option<SourceInfo>) -> Self {
        Self { pat, body_source }
    }

    pub fn get_pat(&self) -> &str {
        &self.pat
    }

    pub fn get_body_source(&self) -> &Option<SourceInfo> {
        &self.body_source
    }
}

#[derive(Clone, Debug)]
pub struct MatchCond {
    match_str: String,
    pub arms_map: BTreeMap<SourceInfo, Arm>,
}

impl MatchCond {
    pub fn new(match_str: String) -> Self {
        Self {
            match_str,
            arms_map: BTreeMap::new(),
        }
    }

    pub fn get_match_str(&self) -> &str {
        &self.match_str
    }

    pub fn add_arm(&mut self, pat_source: SourceInfo, pat: String, body_source: Option<SourceInfo>) {
        self.arms_map
            .insert(pat_source, Arm::new(pat, body_source));
    }

    pub fn get_arms_map(&self) -> &BTreeMap<SourceInfo, Arm> {
        &self.arms_map
    }
}