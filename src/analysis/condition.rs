use std::{
    collections::BTreeMap,
    fmt::{self, Display, Formatter},
};

use super::branchvisitor::SourceInfo;

#[derive(Clone, Debug)]
pub enum Condition {
    Bool(BoolCond),
    For(ForCond),
    Match(MatchCond),
}

#[derive(Clone, Debug)]
pub enum BoolCond {
    Binary(BinaryCond),
    Other(OtherCond),
}

#[derive(Copy, Clone, Debug)]
pub enum BinKind {
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
    Other,
}

impl Display for BinKind {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            BinKind::Eq => write!(f, "=="),
            BinKind::Lt => write!(f, "<"),
            BinKind::Le => write!(f, "<="),
            BinKind::Ne => write!(f, "!="),
            BinKind::Ge => write!(f, ">="),
            BinKind::Gt => write!(f, ">"),
            BinKind::Other => write!(f, "other"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct BinaryCond {
    kind: BinKind,
    expr: String,
    lhs: String,
    rhs: String,
    cmp_with_int: bool,
}

impl BinaryCond {
    pub fn new(kind: BinKind, expr: String, lhs: String, rhs: String, cmp_with_int: bool) -> Self {
        Self {
            kind,
            expr,
            lhs,
            rhs,
            cmp_with_int,
        }
    }

    pub fn get_kind(&self) -> BinKind {
        self.kind
    }

    pub fn get_lhs(&self) -> &str {
        &self.lhs
    }

    pub fn get_rhs(&self) -> &str {
        &self.rhs
    }

    pub fn get_cond_str(&self) -> &str {
        &self.expr
    }

    pub fn cmp_with_int(&self) -> bool {
        self.cmp_with_int
    }

    pub fn get_bound(&self, cond: bool) -> Option<String> {
        match self.kind {
            BinKind::Lt | BinKind::Gt => {
                if !cond {
                    return Some(format!("{} == {}", self.lhs, self.rhs));
                }
            }
            BinKind::Le | BinKind::Ge => {
                if cond {
                    return Some(format!("{} == {}", self.lhs, self.rhs));
                }
            }
            _ => return None,
        }
        None
    }
}

#[derive(Clone, Debug)]
pub struct OtherCond {
    cond_str: String,
}

impl OtherCond {
    pub fn new(cond_str: String) -> Self {
        Self { cond_str }
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
    pat: String,    // TODO: specify the more types of pat, like enum, struct, tuple, etc.
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

    pub fn add_arm(
        &mut self,
        pat_source: SourceInfo,
        pat: String,
        body_source: Option<SourceInfo>,
    ) {
        self.arms_map.insert(pat_source, Arm::new(pat, body_source));
    }

    pub fn get_arms_map(&self) -> &BTreeMap<SourceInfo, Arm> {
        &self.arms_map
    }
}
