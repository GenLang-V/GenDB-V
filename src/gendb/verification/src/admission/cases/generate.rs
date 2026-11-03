//! The case set of one statement instance: find a qualifying tuple, probe which fields matter, then assemble the named
//! cases. Deterministic: the same instance always yields the same cases.
//! With OFFSET/LIMIT also result sizes just below, at and above the window (`limit_window_<n>`).

use super::constants::{TEXT_KEYS, field_domain, small_values, text_fits};
use super::model::{Model, Tuple};
use super::{Case, CaseTables, CaseValue};
use crate::admission::AdmissionError;
use gendb_frontend::columns::SourceType;
use serde_json::{Value, json};
use std::collections::BTreeSet;

/// Pseudo-random tuples tried before the search gives up.
const SEARCH_TRIES: u64 = 20_000;
/// A LIMIT/OFFSET tie case never has more groups than this.
const MAX_TIE_GROUPS: usize = 200;

/// What probing the fields of the base tuple found.
struct FieldProbe {
    /// Fields whose small values all keep the base qualifying (varied freely by value cases).
    free: Vec<usize>,
    /// `(field, first value of the other qualification class)` between neighbouring candidates.
    transitions: Vec<(usize, i128)>,
    /// Variants of the base that do not qualify.
    non_qualifying: Vec<Tuple>,
}

impl Model<'_> {
    /// The case set of this instance with generation facts (`worker_counts`: the configured worker counts;
    /// `max_workers`: the ABI's worker bound).
    pub fn generate(&self, worker_counts: &[usize], max_workers: usize) -> Result<(Vec<Case>, Value), AdmissionError> {
        let default = self.default_tuple();
        let (found, search) = self.search(&default)?;
        let qualifying = found.is_some();
        let base = found.unwrap_or(default);
        let keys = if qualifying { self.varied_group_keys(&base)? } else { vec![] };
        let probe = self.probe_fields(&base, qualifying)?;
        let (shared, shared_tables) = if qualifying { self.share_rows(&base)? } else { (base.clone(), vec![]) };
        let shape = CaseShape { model: self, base: &base, shared: &shared, keys: &keys, free: &probe.free };
        let mut cases = vec![Case { name: "empty_input".into(), tables: vec![vec![]; self.declaration.tables.len()] }];
        shape.push_boundary_cases(&mut cases, &probe);
        shape.push_group_and_tie_cases(&mut cases, qualifying, max_workers);
        shape.push_value_cases(&mut cases);
        shape.push_null_cases(&mut cases);
        let join_info = shape.push_size_and_join_cases(&mut cases, &probe.non_qualifying, worker_counts);
        let info = json!({"qualifying_tuple_found":qualifying,"search":search,"base":format!("{base:?}"),
            "companion_tables_with_one_shared_row":shared_tables.iter().map(|j| &self.declaration.tables[*j].name).collect::<Vec<_>>(),
            "occurrences":self.occurrence_table.iter().enumerate().map(|(o, j)| json!({"occurrence":o,"table":self.declaration.tables[*j].name})).collect::<Vec<_>>(),
            "targeted_candidates":(0..self.slots.len()).filter(|p| !self.targeted[*p].is_empty()).map(|p| json!({"slot":self.slot_label(p),"values":self.targeted[p].len()})).collect::<Vec<_>>(),
            "group_key_slots_varied":keys.iter().map(|p| self.slot_label(*p)).collect::<Vec<_>>(),
            "non_qualifying_rows_found":probe.non_qualifying.len(),
            "free_fields":probe.free.iter().map(|p| self.slot_label(*p)).collect::<Vec<_>>(),
            "transitions":probe.transitions.iter().map(|(p, x)| json!({"field":self.slot_label(*p),"first_value_of_other_class":x.to_string()})).collect::<Vec<_>>(),
            "joins":join_info,"evaluator_runs":self.runs.get()});
        Ok((cases, info))
    }

    /// Every field at its base value, equality classes consistent, group keys at alternating key values.
    fn default_tuple(&self) -> Tuple {
        let mut base: Tuple = self
            .occurrence_table
            .iter()
            .map(|j| (0..self.declaration.tables[*j].columns.len()).map(|_| CaseValue::Num(0)).collect())
            .collect();
        for p in 0..self.slots.len() {
            let v = self.base_value(p);
            self.put(&mut base, p, v);
        }
        for class in &self.classes {
            let v = self.get(&base, class[0]);
            self.set_class(&mut base, class[0], &v);
        }
        for (g, p) in self.key_slots.iter().enumerate() {
            let v = self.key_value(*p, g % 2);
            self.set_class(&mut base, *p, &v);
        }
        base
    }

    /// Deterministic pseudo-random search for a qualifying tuple (splitmix64 stream), with a coordinate refinement of
    /// the sampled tuple every 64 attempts. `None`: none found.
    fn search(&self, base: &Tuple) -> Result<(Option<Tuple>, Value), AdmissionError> {
        if self.qualifies(base)? {
            return Ok((Some(base.clone()), json!({"method":"default tuple"})));
        }
        let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
        let mut next = move || {
            state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        let candidates: Vec<Vec<CaseValue>> = (0..self.slots.len()).map(|p| self.candidates(p)).collect();
        // One representative per equality class (its smallest slot); setting it sets the class.
        let representatives: Vec<usize> = (0..self.slots.len()).filter(|p| self.class_of(*p).iter().min() == Some(p)).collect();
        for attempt in 0..SEARCH_TRIES {
            let mut t = base.clone();
            for p in &representatives {
                let (targets, all) = (&self.targeted[*p], &candidates[*p]);
                let r = next();
                // 70% of the draws take a targeted value when the slot has one.
                let v = if !targets.is_empty() && r % 10 < 7 { &targets[(r >> 8) as usize % targets.len()] } else { &all[(r >> 8) as usize % all.len()] };
                self.set_class(&mut t, *p, v);
            }
            if self.qualifies(&t)? {
                return Ok((Some(t), json!({"method":"pseudo-random search over per-slot candidates","attempts":attempt + 1})));
            }
            if attempt % 64 == 63 {
                for p in &representatives {
                    for v in &candidates[*p] {
                        let mut u = t.clone();
                        self.set_class(&mut u, *p, v);
                        if self.qualifies(&u)? {
                            return Ok((Some(u), json!({"method":"pseudo-random search + coordinate refinement","attempts":attempt + 1})));
                        }
                    }
                }
            }
        }
        Ok((None, json!({"method":"pseudo-random search over per-slot candidates","attempts":SEARCH_TRIES,"found":false})))
    }

    /// The qualifying `base` with the FROM occurrences of each table holding one shared row (the first occurrence's,
    /// equality classes kept), table by table, wherever the tuple still qualifies; with the tables whose occurrences
    /// share one row in the returned tuple (read from it: a later table's class update may change an earlier table).
    /// The verified evaluator's work on a case is the product of its table sizes (a scalar subquery reruns its own
    /// product per outer row), so fewer distinct companion rows shrink every multi-table case multiplicatively.
    fn share_rows(&self, base: &Tuple) -> Result<(Tuple, Vec<usize>), AdmissionError> {
        let occurrences_of = |j: usize| -> Vec<usize> { (0..self.occurrence_table.len()).filter(|o| self.occurrence_table[*o] == j).collect() };
        let mut t = base.clone();
        for j in 0..self.declaration.tables.len() {
            let occurrences = occurrences_of(j);
            let Some((first, others)) = occurrences.split_first() else { continue };
            if others.is_empty() {
                continue;
            }
            let mut u = t.clone();
            for o in others {
                for k in 0..u[*first].len() {
                    let v = u[*first][k].clone();
                    self.set_class(&mut u, self.slot(*o, k), &v);
                }
            }
            if others.iter().all(|o| u[*o] == u[*first]) && (u == t || self.qualifies(&u)?) {
                t = u;
            }
        }
        let shared = (0..self.declaration.tables.len())
            .filter(|j| {
                let occurrences = occurrences_of(*j);
                occurrences.len() > 1 && occurrences.iter().all(|o| t[*o] == t[occurrences[0]])
            })
            .collect();
        Ok((t, shared))
    }

    /// The value of group key slot `p` in group `g`.
    fn key_value(&self, p: usize, g: usize) -> CaseValue {
        match self.ty(p) {
            SourceType::Utf8 => {
                let text = TEXT_KEYS.get(g).map(|s| s.to_string()).filter(|t| text_fits(self.pg_type(p), t)).unwrap_or_else(|| format!("k{g:03}"));
                CaseValue::Text(text)
            }
            SourceType::Decimal { s, .. } => CaseValue::Num(g as i128 * 10i128.pow(s.min(30)) - 3),
            SourceType::Date32 => CaseValue::Num(9000 + g as i128),
            _ => CaseValue::Num(g as i128 - 5),
        }
    }

    /// Group key slots whose variation keeps the base qualifying (a key constrained by a predicate stays fixed).
    fn varied_group_keys(&self, base: &Tuple) -> Result<Vec<usize>, AdmissionError> {
        let mut keys = vec![];
        for p in &self.key_slots {
            let mut t = base.clone();
            self.set_class(&mut t, *p, &self.key_value(*p, 7));
            if self.qualifies(&t)? {
                keys.push(*p);
            }
        }
        Ok(keys)
    }

    fn is_key(&self, p: usize) -> bool {
        self.class_of(p).iter().any(|q| self.key_slots.contains(q))
    }

    fn in_class(&self, p: usize) -> bool {
        self.class_of(p).len() > 1
    }

    /// Fields outside keys and equality classes: which ones are free, where qualification changes (bisection between
    /// neighbouring candidates), and which variants do not qualify.
    fn probe_fields(&self, base: &Tuple, qualifying: bool) -> Result<FieldProbe, AdmissionError> {
        let mut probe = FieldProbe { free: vec![], transitions: vec![], non_qualifying: vec![] };
        for p in (0..self.slots.len()).filter(|p| !self.is_key(*p) && !self.in_class(*p)) {
            let with = |v: CaseValue| {
                let mut t = base.clone();
                self.put(&mut t, p, v);
                t
            };
            if self.ty(p) == SourceType::Utf8 {
                for v in self.candidates(p) {
                    let variant = with(v);
                    if !self.qualifies(&variant)? {
                        probe.non_qualifying.push(variant);
                        break;
                    }
                }
                continue;
            }
            if qualifying && small_values(self.ty(p)).iter().try_fold(true, |all, x| Ok::<_, AdmissionError>(all && self.qualifies(&with(CaseValue::Num(*x)))?))? {
                probe.free.push(p);
            }
            let mut points: Vec<i128> = self.candidates(p).into_iter().filter_map(|v| if let CaseValue::Num(x) = v { Some(x) } else { None }).collect();
            points.sort_unstable();
            points.dedup();
            let mut qualifies_at = vec![];
            for x in &points {
                qualifies_at.push(self.qualifies(&with(CaseValue::Num(*x)))?);
            }
            for i in 1..points.len() {
                if qualifies_at[i - 1] != qualifies_at[i] {
                    let (mut lo, mut hi) = (points[i - 1], points[i]);
                    while hi - lo > 1 {
                        let mid = lo + (hi - lo) / 2;
                        if self.qualifies(&with(CaseValue::Num(mid)))? == qualifies_at[i - 1] { lo = mid } else { hi = mid }
                    }
                    probe.transitions.push((p, hi));
                }
            }
            if let Some(i) = qualifies_at.iter().position(|q| !q) {
                probe.non_qualifying.push(with(CaseValue::Num(points[i])));
            }
        }
        probe.transitions.sort();
        probe.transitions.dedup();
        Ok(probe)
    }
}

/// The base tuple with its varied keys and free fields: the building block of every non-trivial case.
struct CaseShape<'m, 'a> {
    model: &'m Model<'a>,
    /// The searched tuple: probes, predicate boundaries, one row, groups and ties (occurrences keep their own rows).
    base: &'m Tuple,
    /// The base with one shared row per table where it still qualifies ([`Model::share_rows`]): value cases and the
    /// companions of the join and size cases.
    shared: &'m Tuple,
    keys: &'m [usize],
    free: &'m [usize],
}

impl CaseShape<'_, '_> {
    fn several_occurrences(&self) -> bool {
        self.model.occurrence_table.len() > 1
    }

    /// `from` with key `vary` in group `g` and the other keys in group `g % 2` (`mix`) or 0, and the free fields at
    /// small values chosen by `i` and the field's column (occurrences of one table keep equal rows).
    fn tuple_from(&self, from: &Tuple, g: usize, i: usize, vary: usize, mix: bool) -> Tuple {
        let mut t = from.clone();
        for (k, p) in self.keys.iter().enumerate() {
            let v = self.model.key_value(*p, if k == vary { g } else if mix { g % 2 } else { 0 });
            self.model.set_class(&mut t, *p, &v);
        }
        for p in self.free {
            let values = small_values(self.model.ty(*p));
            let column = self.model.slots[*p].1;
            self.model.put(&mut t, *p, CaseValue::Num(values[(i + column) % values.len()]));
        }
        t
    }

    fn tuple(&self, g: usize, i: usize, vary: usize, mix: bool) -> Tuple {
        self.tuple_from(self.base, g, i, vary, mix)
    }

    /// A row of group `g` (key 0 varies, the others alternate).
    fn row(&self, g: usize, i: usize) -> Tuple {
        self.tuple(g, i, 0, true)
    }

    /// A row of group `g` over the shared-row base.
    fn shared_row(&self, g: usize, i: usize) -> Tuple {
        self.tuple_from(self.shared, g, i, 0, true)
    }

    /// The fewest rows on which every group's rows find their matches: the distinct rows of one shared-row tuple per
    /// group (`groups` of them, free fields constant). Companions of the join and size cases, which enlarge one table or
    /// add rows on top.
    fn companions(&self, groups: usize) -> CaseTables {
        self.database((0..groups).map(|g| self.shared_row(g, 0)).collect())
    }

    /// The database of `tuples` (distinct rows per table when several occurrences share tables).
    fn database(&self, tuples: Vec<Tuple>) -> CaseTables {
        self.model.assemble(&tuples, self.several_occurrences())
    }

    /// `no_qualifying_rows`, `one_row` and `predicate_boundaries`.
    fn push_boundary_cases(&self, cases: &mut Vec<Case>, probe: &FieldProbe) {
        let multi = self.several_occurrences();
        if !probe.non_qualifying.is_empty() {
            let tables = if multi { self.model.assemble(&probe.non_qualifying[..1], false) } else { self.model.assemble(&probe.non_qualifying, false) };
            cases.push(Case { name: "no_qualifying_rows".into(), tables });
        }
        cases.push(Case { name: "one_row".into(), tables: self.database(vec![self.row(0, 0)]) });
        if probe.transitions.is_empty() {
            return;
        }
        let mut tuples = vec![];
        if multi {
            tuples.push(self.row(0, 0));
        }
        for (j, (p, x)) in probe.transitions.iter().enumerate() {
            for (d, v) in [x - 2, x - 1, *x, x + 1].into_iter().enumerate() {
                if field_domain(self.model.ty(*p)).is_some_and(|(lo, hi)| (lo..=hi).contains(&v)) {
                    // With several occurrences only the probed field varies, so the other tables keep the base's rows.
                    let mut t = if multi { self.row(0, 0) } else { self.row(j + d, d) };
                    self.model.put(&mut t, *p, CaseValue::Num(v));
                    tuples.push(t);
                }
            }
        }
        cases.push(Case { name: "predicate_boundaries".into(), tables: self.database(tuples) });
    }

    /// More groups than `max_workers`, ties at the OFFSET/LIMIT boundary, UTF-8 key byte order.
    fn push_group_and_tie_cases(&self, cases: &mut Vec<Case>, qualifying: bool, max_workers: usize) {
        let model = self.model;
        let window_rows = || (model.offset as usize).saturating_add(model.limit.unwrap_or(0) as usize).saturating_add(3).min(MAX_TIE_GROUPS);
        let sliced = model.limit.is_some() || model.offset > 0;
        if !self.keys.is_empty() {
            let groups = max_workers + 6;
            cases.push(Case { name: format!("groups_{groups}"), tables: self.database((0..groups * 2).map(|i| self.row(i % groups, i)).collect()) });
            if sliced {
                // Vary a key that is not an ORDER BY output, so every ORDER BY key stays equal.
                let tie_key = self.keys.iter().position(|p| !model.ordered_key(*p)).unwrap_or(0);
                cases.push(Case { name: "limit_boundary_ties".into(), tables: self.database((0..window_rows()).map(|g| self.tuple(g, 0, tie_key, false)).collect()) });
            }
            if self.keys.iter().any(|p| model.ty(*p) == SourceType::Utf8) {
                cases.push(Case {
                    name: "utf8_keys_byte_order".into(),
                    tables: self.database((0..TEXT_KEYS.len() * 2).map(|i| self.row(i % TEXT_KEYS.len(), i)).collect()),
                });
            }
        } else if sliced && qualifying {
            // Without group keys: several qualifying rows that tie on every ORDER BY key.
            cases.push(Case { name: "limit_boundary_ties".into(), tables: model.assemble(&vec![self.base.clone(); window_rows()], false) });
        }
        // Result sizes just below, at and just above the OFFSET + LIMIT window: distinct groups (or rows) whose free
        // fields differ, so the ORDER BY values mostly differ and the window cuts between distinct rows.
        if sliced && qualifying {
            let window = (model.offset as usize).saturating_add(model.limit.unwrap_or(0) as usize);
            for n in [window.saturating_sub(1), window, window + 1] {
                if n == 0 || n > MAX_TIE_GROUPS {
                    continue;
                }
                let tuples: Vec<Tuple> = (0..n).map(|g| if self.keys.is_empty() { self.tuple(0, g, 0, false) } else { self.row(g, g) }).collect();
                cases.push(Case { name: format!("limit_window_{n}"), tables: self.database(tuples) });
            }
        }
    }

    /// Signed values that cancel, AVG display scales, and the extreme values of the declared column domains (over the
    /// shared-row base).
    fn push_value_cases(&self, cases: &mut Vec<Case>) {
        if self.free.is_empty() {
            return;
        }
        let model = self.model;
        let mut signed = vec![];
        for i in 0..6 {
            let mut t = self.shared_row(i % 2, i);
            for p in self.free {
                model.put(&mut t, *p, CaseValue::Num(if i % 2 == 0 { 3 } else { -3 } * (i as i128 + 1)));
            }
            signed.push(t);
        }
        cases.push(Case { name: "signed_values".into(), tables: self.database(signed) });
        // (rows in the group, the first row's value; the others are 0): averages with different display scales.
        let mut scales = vec![];
        for (g, (count, value)) in [(3usize, 1i128), (7, 10), (1, 999_999_999), (2, 12345), (6, 5)].into_iter().enumerate() {
            for i in 0..count {
                let mut t = self.shared_row(g, i);
                for p in self.free {
                    model.put(&mut t, *p, CaseValue::Num(if i == 0 { value } else { 0 }));
                }
                scales.push(t);
            }
        }
        cases.push(Case { name: "avg_display_scales".into(), tables: self.database(scales) });
        for (name, maximum) in [("domain_max_values", true), ("domain_min_values", false)] {
            let mut t = self.shared_row(0, 0);
            for p in self.free {
                if let Some((lo, hi)) = field_domain(model.ty(*p)) {
                    model.put(&mut t, *p, CaseValue::Num(if maximum { hi } else { lo }));
                }
            }
            cases.push(Case { name: name.into(), tables: model.assemble(&[t.clone(), t], false) });
        }
    }

    /// Per nullable delivered column `null_<table>_<column>`: two rows of the shared-row base and the same rows with that
    /// column NULL (in every occurrence of its table); and `all_nullable_null`: a row with every nullable column NULL
    /// beside the same row without NULL. So some case holds a NULL in every nullable column the statement reads.
    fn push_null_cases(&self, cases: &mut Vec<Case>) {
        let model = self.model;
        let nullable: Vec<(usize, usize)> = model
            .declaration
            .tables
            .iter()
            .enumerate()
            .flat_map(|(j, t)| t.columns.iter().enumerate().filter(|(_, c)| c.nullable).map(move |(k, _)| (j, k)))
            .collect();
        if nullable.is_empty() {
            return;
        }
        let set_null = |t: &mut Tuple, j: usize, k: usize| {
            for p in 0..model.slots.len() {
                let (o, column) = model.slots[p];
                if model.occurrence_table[o] == j && column == k {
                    model.put(t, p, CaseValue::Null);
                }
            }
        };
        for &(j, k) in &nullable {
            let mut tuples = vec![];
            for g in 0..2 {
                let row = self.shared_row(g, g);
                let mut with_null = row.clone();
                set_null(&mut with_null, j, k);
                tuples.extend([row, with_null]);
            }
            let table = &model.declaration.tables[j];
            cases.push(Case { name: format!("null_{}_{}", table.name, table.columns[k].name), tables: self.database(tuples) });
        }
        let row = self.shared_row(0, 0);
        let mut all = row.clone();
        for &(j, k) in &nullable {
            set_null(&mut all, j, k);
        }
        cases.push(Case { name: "all_nullable_null".into(), tables: self.database(vec![row, all]) });
    }

    /// Row counts around 32, 64 and every worker count; with several occurrences also each table empty in turn,
    /// duplicate matches on every side and rows without a match. Returns the join facts for the generation record.
    fn push_size_and_join_cases(&self, cases: &mut Vec<Case>, non_qualifying: &[Tuple], worker_counts: &[usize]) -> Value {
        let model = self.model;
        let mixed: Vec<Tuple> = (0..8)
            .map(|i| if i % 4 == 3 && !non_qualifying.is_empty() { non_qualifying[i % non_qualifying.len()].clone() } else { self.row(i % 3, i) })
            .collect();
        let mut sizes = BTreeSet::from([1usize, 2, 31, 32, 33, 63, 64, 65]);
        for w in worker_counts {
            sizes.extend([w.saturating_sub(1), *w, w + 1].into_iter().filter(|n| *n > 0));
        }
        if !self.several_occurrences() {
            for n in sizes {
                cases.push(Case { name: format!("rows_{n}"), tables: model.assemble(&mixed.iter().cycle().take(n).cloned().collect::<Vec<_>>(), false) });
            }
            return Value::Null;
        }
        let table_count = model.declaration.tables.len();
        let occurrences = model.occurrence_table.len();
        let pair = self.database(vec![self.row(0, 0), self.row(1, 1)]);
        for j in 0..table_count {
            let mut tables = pair.clone();
            tables[j].clear();
            cases.push(Case { name: format!("empty_table_t{j}"), tables });
        }
        // Duplicate matches on every side: table j holds 2 + j % 2 copies of each companion row per group (differing in
        // the free fields; a third copy is an exact duplicate); two groups when a group key is varied, else one.
        let groups = if self.keys.is_empty() { 1 } else { 2 };
        let copies: Vec<usize> = (0..table_count).map(|j| 2 + j % 2).collect();
        let mut tables: CaseTables = vec![vec![]; table_count];
        for g in 0..groups {
            for (j, count) in copies.iter().enumerate() {
                for c in 0..*count {
                    tables[j].extend(self.database(vec![self.shared_row(g, if c == 2 { 0 } else { c })]).swap_remove(j));
                }
            }
        }
        cases.push(Case { name: "many_to_many".into(), tables });
        // Rows without a match: every occurrence with an equality-class field adds a row whose class fields hold a value
        // no other occurrence has; every non-qualifying variant adds its first differing occurrence's row.
        let mut tables = self.companions(2);
        for (o, j) in model.occurrence_table.iter().enumerate() {
            let mut r = self.shared_row(0, 0)[o].clone();
            let mut changed = false;
            for (p, (po, k)) in model.slots.iter().enumerate() {
                if *po == o && model.in_class(p) {
                    r[*k] = model.key_value(p, 40 + o);
                    changed = true;
                }
            }
            if changed {
                tables[*j].push(r);
            }
        }
        for variant in non_qualifying {
            if let Some(o) = (0..occurrences).find(|o| variant[*o] != self.base[*o]) {
                tables[model.occurrence_table[o]].push(variant[o].clone());
            }
        }
        cases.push(Case { name: "unmatched_rows".into(), tables });
        let base_tables = self.companions(3);
        for j in 0..table_count {
            let first = model.occurrence_table.iter().position(|x| *x == j).expect("every delivered table has an occurrence");
            for n in &sizes {
                let mut tables = base_tables.clone();
                tables[j] = mixed.iter().cycle().take(*n).map(|t| t[first].clone()).collect();
                cases.push(Case { name: format!("rows_t{j}_{n}"), tables });
            }
        }
        json!({"equality_classes":model.classes.iter().map(|c| c.iter().map(|p| model.slot_label(*p)).collect::<Vec<_>>()).collect::<Vec<_>>(),
            "many_to_many_copies_per_group_and_table":copies,"many_to_many_groups":groups})
    }
}
