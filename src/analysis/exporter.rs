#[derive(Debug, Clone, serde::Serialize)]
pub struct JsonData {
    name: String,
    codes: Vec<String>,
    loc: (usize, usize),
    con_chains: Vec<CondChain>,
}

impl JsonData {
    pub fn new(name: String, codes: Vec<String>, loc: (usize, usize)) -> Self {
        Self {
            name,
            codes,
            loc,
            con_chains: vec![],
        }
    }

    pub fn chain_len(&self) -> usize {
        self.con_chains.len()
    }

    pub fn add_chain(&mut self, mut chain: CondChain) {
        chain.id = self.con_chains.len() + 1;
        self.con_chains.push(chain);
    }
}

#[derive(Debug, Clone, serde::Serialize)]
pub struct CondChain {
    id: usize,
    conds: Vec<Cond>,
    path: Vec<usize>,
}

impl CondChain {
    pub fn new(conds: Vec<Cond>, path: Vec<usize>) -> Self {
        Self {
            id: 0,
            conds,
            path,
        }
    }
}

#[derive(Debug, Clone, serde::Serialize)]
pub struct Cond {
    pub cond: String,
    pub value: String,
    pub line: usize,
    pub bound: Option<String>,
}

impl Cond {
    pub fn new(cond: String, value: String, line: usize) -> Self {
        Self {
            cond,
            value,
            line,
            bound: None,
        }
    }
}
