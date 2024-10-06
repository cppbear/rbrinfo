#[derive(Debug)]
pub enum Condition {
    Bool(BoolCond),
    For(ForCond),
    Match(MatchCond),
}

#[derive(Debug)]
pub enum CmpIntKind {
    No,
    Eq,
    Ne,
}

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug)]
pub struct MatchCond {
    match_str: String,
    // arms: Vec<Arm>,
}
