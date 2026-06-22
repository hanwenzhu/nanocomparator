//! A translation of `Comparator/Compare.lean`.

use crate::eq::{declar_equal, declar_info_equal};
use crate::util::{new_fx_hash_set, FxHashSet};
use nanoda_lib::env::{Declar, DeclarInfo};
use nanoda_lib::expr::Expr;
use nanoda_lib::util::{ExportFile, ExprPtr, NamePtr};

/// `primitiveTargets` in Comparator.
pub const PRIMITIVE_TARGETS: &[&str] = &[
    // "Nat.zero",
    // "Nat.succ",
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.pow",
    "Nat.gcd",
    "Nat.div",
    "Nat.mod",
    "Nat.beq",
    "Nat.ble",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "String.ofList",
];

/// Same as `Lean.ConstantInfo.value?`
pub fn declar_value<'t>(declar: &Declar<'t>, allow_opaque: bool) -> Option<ExprPtr<'t>> {
    match declar {
        Declar::Definition { val, .. } => Some(*val),
        Declar::Theorem { val, .. } => {
            if allow_opaque {
                Some(*val)
            } else {
                None
            }
        }
        Declar::Opaque { val, .. } => {
            if allow_opaque {
                Some(*val)
            } else {
                None
            }
        }
        _ => None,
    }
}

pub fn find_const_from_str<'a, 'b>(f: &'a ExportFile<'b>, name: &str) -> Option<(NamePtr<'b>, &'a Declar<'b>)> {
    let n = f.dag.find_name(name)?;
    let d = f.declars.get(&n)?;
    Some((n, d))
}

/// A constant identified in both files: its name pointer in the challenge and in the solution.
/// TODO: Can this be eliminated in place of actual names?
pub type NamePair<'c, 's> = (NamePtr<'c>, NamePtr<'s>);

/// Similar to `Lean.Expr.getUsedConstants` but returns a list of (challenge [`NamePtr`], solution [`NamePtr`])
/// because although the names are equal, the [`NamePtr`]s are specific to each file.
pub fn get_used_constants_pair<'c, 's>(
    c: &ExportFile<'c>,
    ce: ExprPtr<'c>,
    s: &ExportFile<'s>,
    se: ExprPtr<'s>,
) -> Vec<NamePair<'c, 's>> {
    fn go<'c, 's>(
        c: &ExportFile<'c>,
        ce: ExprPtr<'c>,
        s: &ExportFile<'s>,
        se: ExprPtr<'s>,
        visited: &mut FxHashSet<(ExprPtr<'c>, ExprPtr<'s>)>,
        seen: &mut FxHashSet<NamePtr<'c>>,
        out: &mut Vec<NamePair<'c, 's>>,
    ) {
        if !visited.insert((ce, se)) {
            return;
        }
        match (c.dag.read_expr(ce), s.dag.read_expr(se)) {
            (Expr::Const { name: n1, .. }, Expr::Const { name: n2, .. }) => {
                if seen.insert(n1) {
                    out.push((n1, n2));
                }
            }
            (Expr::App { fun: f1, arg: a1, .. }, Expr::App { fun: f2, arg: a2, .. }) => {
                go(c, f1, s, f2, visited, seen, out);
                go(c, a1, s, a2, visited, seen, out);
            }
            (Expr::Pi { binder_type: t1, body: b1, .. }, Expr::Pi { binder_type: t2, body: b2, .. })
            | (Expr::Lambda { binder_type: t1, body: b1, .. }, Expr::Lambda { binder_type: t2, body: b2, .. }) => {
                go(c, t1, s, t2, visited, seen, out);
                go(c, b1, s, b2, visited, seen, out);
            }
            (
                Expr::Let { binder_type: t1, val: v1, body: b1, .. },
                Expr::Let { binder_type: t2, val: v2, body: b2, .. },
            ) => {
                go(c, t1, s, t2, visited, seen, out);
                go(c, v1, s, v2, visited, seen, out);
                go(c, b1, s, b2, visited, seen, out);
            }
            (Expr::Proj { structure: st1, .. }, Expr::Proj { structure: st2, .. }) => {
                go(c, st1, s, st2, visited, seen, out)
            }
            _ => {}
        }
    }

    let mut visited = new_fx_hash_set();
    let mut seen = new_fx_hash_set();
    let mut out = Vec::new();
    go(c, ce, s, se, &mut visited, &mut seen, &mut out);
    out
}

/// Similar to `Comparator.runForUsedConsts` from Comparator.
pub fn run_for_used_constants_pair<'c, 's, F>(
    c: &ExportFile<'c>,
    dc: &Declar<'c>,
    s: &ExportFile<'s>,
    ds: &Declar<'s>,
    mut f: F,
) where
    F: FnMut(NamePair<'c, 's>),
{
    for pair in get_used_constants_pair(c, dc.info().ty, s, ds.info().ty) {
        f(pair);
    }
    f((dc.info().name, ds.info().name));
    if let (Some(vc), Some(vs)) = (declar_value(dc, true), declar_value(ds, true)) {
        for pair in get_used_constants_pair(c, vc, s, vs) {
            f(pair);
        }
    }
    match (dc, ds) {
        (Declar::Inductive(i1), Declar::Inductive(i2)) => {
            for (a, b) in i1.all_ctor_names.iter().zip(i2.all_ctor_names.iter()) {
                f((*a, *b));
            }
            for (a, b) in i1.all_ind_names.iter().zip(i2.all_ind_names.iter()) {
                f((*a, *b));
            }
        }
        (Declar::Constructor(c1), Declar::Constructor(c2)) => f((c1.inductive_name, c2.inductive_name)),
        (Declar::Recursor(r1), Declar::Recursor(r2)) => {
            for (ru1, ru2) in r1.rec_rules.iter().zip(r2.rec_rules.iter()) {
                f((ru1.ctor_name, ru2.ctor_name));
                for pair in get_used_constants_pair(c, ru1.val, s, ru2.val) {
                    f(pair);
                }
            }
        }
        _ => {}
    }
}

// The below is a line-by-line translation of `Comparator/Compare.lean`.

/// `Comparator.Compare.CompareM` from Comparator.
struct CompareCtx<'a, 'c, 's> {
    challenge: &'a ExportFile<'c>,
    solution: &'a ExportFile<'s>,
    definition_targets: FxHashSet<NamePtr<'c>>,
    worklist: Vec<NamePair<'c, 's>>,
    checked: FxHashSet<NamePtr<'c>>,
}

impl<'a, 'c, 's> CompareCtx<'a, 'c, 's> {
    /// `Comparator.Compare.addWorklist` from Comparator.
    fn add_worklist(&mut self, n: NamePair<'c, 's>) {
        if !self.checked.contains(&n.0) {
            self.worklist.push(n);
        }
    }

    /// `Comparator.Compare.addRelevantConsts` from Comparator.
    fn add_relevant_consts(&mut self, dc: &'a Declar<'c>, ds: &'a Declar<'s>) {
        run_for_used_constants_pair(self.challenge, dc, self.solution, ds, |n| self.add_worklist(n));
    }

    /// `Comparator.Compare.loop` from Comparator.
    fn loop_(&mut self) -> Result<(), String> {
        let Some((tc, ts)) = self.worklist.pop() else {
            return Ok(());
        };

        if self.checked.contains(&tc) {
            self.loop_()
        } else {
            let Some(challenge_const) = self.challenge.declars.get(&tc) else {
                let target = self.challenge.dag.name_to_string(tc);
                return Err(format!("Const not found in challenge '{target}'"));
            };
            let Some(solution_const) = self.solution.declars.get(&ts) else {
                let target = self.challenge.dag.name_to_string(tc);
                return Err(format!("Const not found in solution '{target}'"));
            };

            if self.definition_targets.contains(&tc) {
                for pair in get_used_constants_pair(
                    self.challenge,
                    challenge_const.info().ty,
                    self.solution,
                    solution_const.info().ty,
                ) {
                    self.add_worklist(pair);
                }
            } else {
                if !declar_equal(self.challenge, challenge_const, self.solution, solution_const) {
                    let target = self.challenge.dag.name_to_string(tc);
                    return Err(format!("Const does not match between challenge and target '{target}'"));
                }
                self.add_relevant_consts(challenge_const, solution_const);
            }

            self.checked.insert(tc);
            self.loop_()
        }
    }
}

/// Similar to `Comparator.Compare.definitionHoleMatches` from Comparator (note nanoda does not record `safety`).
pub fn definition_hole_matches<'c, 's>(
    c: &ExportFile<'c>,
    hc: &DeclarInfo<'c>,
    s: &ExportFile<'s>,
    hs: &DeclarInfo<'s>,
) -> bool {
    declar_info_equal(c, hc, s, hs)
}

/// Same as `Comparator.Compare.compareAt` from Comparator.
pub fn compare_at<'c, 's>(
    challenge: &ExportFile<'c>,
    solution: &ExportFile<'s>,
    theorem_targets: &[&str],
    definition_targets: &[&str],
    primitive: &[&str],
) -> Result<(), String> {
    let mut worklist: Vec<NamePair<'c, 's>> = Vec::new();

    for name in primitive {
        let Some((cn, _)) = find_const_from_str(challenge, name) else {
            return Err(format!("Const not found in challenge: '{name}'"));
        };
        let Some((sn, _)) = find_const_from_str(solution, name) else {
            return Err(format!("Const not found in solution: '{name}'"));
        };
        worklist.push((cn, sn));
    }

    for target in theorem_targets {
        let Some((_, challenge_const)) = find_const_from_str(challenge, target) else {
            return Err(format!("Const not found in challenge: '{target}'"));
        };

        let Some((_, solution_const)) = find_const_from_str(solution, target) else {
            return Err(format!("Const not found in solution: '{target}'"));
        };

        let (challenge_const, solution_const) = match (challenge_const, solution_const) {
            (Declar::Theorem { .. }, Declar::Theorem { .. }) | (Declar::Axiom { .. }, Declar::Axiom { .. }) => {
                (challenge_const.info(), solution_const.info())
            }
            _ => return Err(format!("Challenge and solution constant kind don't match: '{target}'")),
        };

        if !declar_info_equal(challenge, challenge_const, solution, solution_const) {
            return Err(format!("Challenge and solution theorem statement do not match: '{target}'"));
        }

        for pair in get_used_constants_pair(challenge, challenge_const.ty, solution, solution_const.ty) {
            worklist.push(pair);
        }
    }

    let mut definition_target_ptrs: FxHashSet<NamePtr<'c>> = new_fx_hash_set();
    for target in definition_targets {
        let Some((cn, challenge_const)) = find_const_from_str(challenge, target) else {
            return Err(format!("Const not found in challenge: '{target}'"));
        };
        let Some((sn, solution_const)) = find_const_from_str(solution, target) else {
            return Err(format!("Const not found in solution: '{target}'"));
        };

        let Declar::Definition { info: challenge_const, .. } = challenge_const else {
            return Err(format!("Challenge constant is not a definition: '{target}'"));
        };
        let Declar::Definition { info: solution_const, .. } = solution_const else {
            return Err(format!("Solution constant is not a definition: '{target}'"));
        };
        if !definition_hole_matches(challenge, challenge_const, solution, solution_const) {
            return Err(format!("Const does not match between challenge and target '{target}'"));
        }

        definition_target_ptrs.insert(cn);
        worklist.push((cn, sn));
    }

    let definition_targets = definition_target_ptrs;
    CompareCtx { challenge, solution, definition_targets, worklist, checked: new_fx_hash_set() }.loop_()
}
