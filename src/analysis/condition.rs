use super::sourceinfo::SourceInfo;
use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Display, Formatter},
    hash::{Hash, Hasher},
};

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize)]
pub enum Condition {
    Bool(BoolCond),
    For(ForCond),
    Match(MatchCond),
    Try(String),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize)]
pub enum BoolCond {
    Binary(BinaryCond),
    Other(String),
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, serde::Serialize)]
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

impl BoolCond {
    pub fn get_cond_str(&self) -> String {
        match self {
            BoolCond::Binary(b) => b.get_cond_str(),
            BoolCond::Other(s) => s.clone(),
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize)]
pub struct BinaryCond {
    pub kind: BinKind,
    pub expr: String,
    pub lhs: String,
    pub rhs: String,
    pub cmp_with_int: bool,
}

impl BinaryCond {
    // pub fn has_bound(&self, cond: bool) -> bool {
    //     match self.kind {
    //         BinKind::Lt | BinKind::Gt => {
    //             if !cond {
    //                 return true;
    //             }
    //         }
    //         BinKind::Le | BinKind::Ge => {
    //             if cond {
    //                 return true;
    //             }
    //         }
    //         _ => return false,
    //     }
    //     false
    // }

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

    pub fn eq_with_int(&self) -> bool {
        self.cmp_with_int && self.kind == BinKind::Eq
    }

    pub fn ne_with_int(&self) -> bool {
        self.cmp_with_int && self.kind == BinKind::Ne
    }
}

impl BinaryCond {
    pub fn get_cond_str(&self) -> String {
        self.expr.clone()
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize)]
pub struct ForCond {
    pub iter_var: String,
    pub iter_range: String,
}

impl ForCond {
    pub fn get_cond_str(&self) -> String {
        format!("{} in {}", self.iter_var, self.iter_range)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub enum PattKind {
    Enum(usize),
    StructLike(HashMap<usize, (Option<u128>, SourceInfo)>),
    Other(Option<u128>),
    Wild,
}

impl Hash for PattKind {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            PattKind::Enum(idx) => idx.hash(state),
            PattKind::StructLike(fields) => {
                for (key, (opt, _source_info)) in fields {
                    key.hash(state);
                    opt.hash(state);
                    _source_info.hash(state);
                }
            }
            PattKind::Other(val) => val.hash(state),
            PattKind::Wild => "wild".hash(state),
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize)]
pub struct Patt {
    pub pat_str: String,
    pub kind: PattKind,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct Arm {
    pub pat: Patt,
    pub guard: Option<HashMap<SourceInfo, HashSet<Condition>>>,
    pub body_source: Option<SourceInfo>,
}

impl Hash for Arm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.pat.hash(state);
        if let Some(guard) = &self.guard {
            for (key, val) in guard {
                key.hash(state);
                for cond in val {
                    cond.hash(state);
                }
            }
        }
        self.body_source.hash(state);
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize)]
pub enum MatchKind {
    Enum(Vec<String>),
    StructLike(Option<Vec<String>>),
    Other,
}

impl MatchKind {
    pub fn get_field_name(&self, idx: usize) -> String {
        match self {
            MatchKind::Enum(variants) => variants[idx].clone(),
            MatchKind::StructLike(Some(fields)) => fields[idx].clone(),
            _ => idx.to_string(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct MatchCond {
    pub match_source: SourceInfo,
    pub match_str: String,
    pub match_kind: MatchKind,
    pub arms: HashMap<SourceInfo, Arm>,
}

impl Hash for MatchCond {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.match_source.hash(state);
        self.match_str.hash(state);
        self.match_kind.hash(state);
        for (key, val) in &self.arms {
            key.hash(state);
            val.hash(state);
        }
    }
}

impl MatchCond {
    pub fn new(match_source: SourceInfo, match_str: String, match_kind: MatchKind) -> Self {
        Self {
            match_source,
            match_str,
            match_kind,
            arms: HashMap::new(),
        }
    }
}

impl MatchCond {
    pub fn get_cond_str(&self, pat_source: SourceInfo) -> String {
        format!(
            "{} is {}",
            self.match_str,
            self.arms.get(&pat_source).unwrap().pat.pat_str
        )
    }
}
