//! Question 6: bound the request prefix list reused on each element visit.

use super::Analysis;
use crate::facts::{Facts, Id, Lang, ResultFlow, ResultFlowKind};
use std::collections::{BTreeMap, HashMap, HashSet};

mod bergshamra;
mod direct;

const RULE: &str = "prefix-work";

impl Analysis<'_> {
    pub(super) fn prefix_work(&mut self) {
        if !self.cfg.q6.prefix_work {
            return;
        }
        if self.f.files.iter().any(|file| file.repo != 0) {
            self.not_checked.entry(6).or_default().push(
                "prefix-work needs a per-repository scan to identify the reviewed sources".into(),
            );
            return;
        }
        let entries: HashSet<_> = self.untrusted_entries().into_iter().collect();
        if entries.is_empty() {
            return;
        }
        let texts: BTreeMap<_, _> = self
            .texts
            .iter()
            .map(|(path, source)| (path.as_str(), source.as_str()))
            .collect();
        let flows = ResultFlows::new(self.f);
        let reach = self.untrusted_reach();
        self.direct_prefix_work(&texts, &entries, &flows);
        self.bergshamra_prefix_work(&texts, &reach, &flows);
    }

    fn prefix_candidate(&self, func: Id) -> bool {
        let fun = &self.f.funcs[func as usize];
        let file = &self.f.files[fun.file as usize];
        file.lang == Lang::Rust && !file.test && !fun.test
    }
}

type Texts<'a> = BTreeMap<&'a str, &'a str>;

struct ResultFlows<'a> {
    facts: &'a Facts,
    by_function: HashMap<Id, Vec<&'a ResultFlow>>,
}

impl<'a> ResultFlows<'a> {
    fn new(facts: &'a Facts) -> Self {
        let mut by_function: HashMap<_, Vec<_>> = HashMap::new();
        for flow in &facts.result_flows {
            let func = facts.sites[flow.site as usize].func;
            by_function.entry(func).or_default().push(flow);
        }
        Self { facts, by_function }
    }

    fn propagated<'b>(
        &'b self,
        func: Id,
        call: &'b str,
    ) -> impl Iterator<Item = &'b ResultFlow> + 'b {
        self.in_function(func).filter(move |flow| {
            matches!(&flow.kind, ResultFlowKind::Propagate { call: actual } if actual == call)
        })
    }

    fn rejecting<'b>(
        &'b self,
        func: Id,
        condition: &'b str,
        returned: &'b str,
    ) -> impl Iterator<Item = &'b ResultFlow> + 'b {
        self.in_function(func).filter(move |flow| {
            matches!(&flow.kind, ResultFlowKind::Reject { condition: actual, returned: exit }
                if actual == condition && exit == returned)
        })
    }

    fn in_function(&self, func: Id) -> impl Iterator<Item = &ResultFlow> {
        self.by_function
            .get(&func)
            .into_iter()
            .flatten()
            .copied()
            .filter(|flow| !self.facts.sites[flow.site as usize].ctx.in_lambda)
    }
}

/// The accepted size of one value in one function on paths after `check` succeeds.
struct Cardinality<'a> {
    value: &'a str,
    check: Id,
    members: usize,
    member_bytes: usize,
}
