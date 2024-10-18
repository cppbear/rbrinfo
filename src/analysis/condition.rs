use std::{
    collections::HashMap,
    fmt::{self, Display, Formatter},
};

use super::sourceinfo::SourceInfo;

#[derive(Clone, Debug)]
pub enum Condition {
    Bool(BoolCond),
    For(ForCond),
    Match(MatchCond),
}

#[derive(Clone, Debug)]
pub enum BoolCond {
    Binary(BinaryCond),
    Other(String),
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

impl BoolCond {
    pub fn get_cond_str(&self) -> String {
        match self {
            BoolCond::Binary(b) => b.get_cond_str(),
            BoolCond::Other(s) => s.clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct BinaryCond {
    pub kind: BinKind,
    pub expr: String,
    pub lhs: String,
    pub rhs: String,
    pub cmp_with_int: bool,
}

impl BinaryCond {
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

impl BinaryCond {
    pub fn get_cond_str(&self) -> String {
        self.expr.clone()
    }
}

#[derive(Clone, Debug)]
pub struct ForCond {
    pub iter_var: String,
    pub iter_range: String,
}

impl ForCond {
    pub fn get_cond_str(&self) -> String {
        format!("{} in {}", self.iter_var, self.iter_range)
    }
}

#[derive(Clone, Debug)]
pub enum PattKind {
    Enum(usize),
    StructOrTuple(HashMap<usize, Option<u128>>),
    Other,
}

#[derive(Clone, Debug)]
pub struct Patt {
    pub pat_str: String,
    pub kind: PattKind,
}

#[derive(Clone, Debug)]
pub struct Arm {
    pub pat: Patt,
    pub guard: Option<HashMap<SourceInfo, Condition>>,
    pub body_source: SourceInfo,
}

#[derive(Clone, Debug)]
pub struct MatchCond {
    pub match_str: String,
    pub arms: HashMap<SourceInfo, Arm>,
}

impl MatchCond {
    pub fn new(match_str: String) -> Self {
        Self {
            match_str,
            arms: HashMap::new(),
        }
    }

    // pub fn add_arm(
    //     &mut self,
    //     pat_source: SourceInfo,
    //     pat_str: String,
    //     kind: PattKind,
    //     body_source: Option<SourceInfo>,
    // ) {
    //     self.arms.insert(
    //         pat_source,
    //         Arm {
    //             pat_str,
    //             kind,
    //             guard: None,
    //             body_source,
    //         },
    //     );
    // }
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
