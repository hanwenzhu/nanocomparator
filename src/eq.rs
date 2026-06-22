//! Equality comparisons between Lean expressions and constants from two Lean [`ExportFile`]s.
//!
//! Cf. `lean4/src/kernel/expr_eq_fn.cpp`, but allows cross-[`ExportFile`] comparison.

use crate::util::{new_fx_hash_set, FxHashSet};
use nanoda_lib::env::{Declar, DeclarInfo};
use nanoda_lib::expr::Expr;
use nanoda_lib::level::Level;
use nanoda_lib::name::Name;
use nanoda_lib::util::{BigUintPtr, ExportFile, ExprPtr, LevelPtr, LevelsPtr, NamePtr, StringPtr};

/// Memoises expression equality: containment means equality (cf. `m_cache` in `expr_eq_fn`).
type EqCache<'a, 'b> = FxHashSet<(ExprPtr<'a>, ExprPtr<'b>)>;

/// Similar to `expr_eq_fn` in Lean kernel; re-instantiated for each comparison.
struct EqCtx<'a, 'b> {
    fa: &'a ExportFile<'a>,
    fb: &'b ExportFile<'b>,
    cache: EqCache<'a, 'b>,
    compare_binder_info: bool,
}

impl<'a, 'b> EqCtx<'a, 'b> {
    fn new(fa: &'a ExportFile<'a>, fb: &'b ExportFile<'b>, compare_binder_info: bool) -> Self {
        Self { fa, fb, cache: new_fx_hash_set(), compare_binder_info }
    }

    fn string_eq(&self, sa: StringPtr<'a>, sb: StringPtr<'b>) -> bool {
        self.fa.dag.read_string(sa) == self.fb.dag.read_string(sb)
    }

    fn bignum_eq(&self, pa: BigUintPtr<'a>, pb: BigUintPtr<'b>) -> bool {
        self.fa.dag.read_bignum(pa) == self.fb.dag.read_bignum(pb)
    }

    fn name_eq(&self, na: NamePtr<'a>, nb: NamePtr<'b>) -> bool {
        match (self.fa.dag.read_name(na), self.fb.dag.read_name(nb)) {
            (Name::Anon, Name::Anon) => true,
            (Name::Str(pa, sa, _), Name::Str(pb, sb, _)) => {
                self.fa.dag.read_string(sa) == self.fb.dag.read_string(sb) && self.name_eq(pa, pb)
            }
            (Name::Num(pa, ia, _), Name::Num(pb, ib, _)) => ia == ib && self.name_eq(pa, pb),
            _ => false,
        }
    }

    fn names_eq(&self, sa: &[NamePtr<'a>], sb: &[NamePtr<'b>]) -> bool {
        sa.len() == sb.len() && sa.iter().zip(sb.iter()).all(|(na, nb)| self.name_eq(*na, *nb))
    }

    fn level_eq(&self, la: LevelPtr<'a>, lb: LevelPtr<'b>) -> bool {
        match (self.fa.dag.read_level(la), self.fb.dag.read_level(lb)) {
            (Level::Zero, Level::Zero) => true,
            (Level::Succ(xa, _), Level::Succ(xb, _)) => self.level_eq(xa, xb),
            (Level::Max(xa, ya, _), Level::Max(xb, yb, _)) | (Level::IMax(xa, ya, _), Level::IMax(xb, yb, _)) => {
                self.level_eq(xa, xb) && self.level_eq(ya, yb)
            }
            (Level::Param(na, _), Level::Param(nb, _)) => self.name_eq(na, nb),
            _ => false,
        }
    }

    fn levels_eq(&self, ua: LevelsPtr<'a>, ub: LevelsPtr<'b>) -> bool {
        let la = self.fa.dag.read_levels(ua);
        let lb = self.fb.dag.read_levels(ub);
        la.len() == lb.len() && la.iter().zip(lb.iter()).all(|(la, lb)| self.level_eq(*la, *lb))
    }

    fn expr_eq(&mut self, ea: ExprPtr<'a>, eb: ExprPtr<'b>) -> bool {
        if self.cache.contains(&(ea, eb)) {
            return true;
        }

        // Note: hash of Expr in nanoda_lib is file-dependent, so we do not use it here.

        let ok = match (self.fa.dag.read_expr(ea), self.fb.dag.read_expr(eb)) {
            (Expr::Var { dbj_idx: i, .. }, Expr::Var { dbj_idx: j, .. }) => i == j,
            (Expr::StringLit { ptr: pa, .. }, Expr::StringLit { ptr: pb, .. }) => self.string_eq(pa, pb),
            (Expr::NatLit { ptr: pa, .. }, Expr::NatLit { ptr: pb, .. }) => self.bignum_eq(pa, pb),
            (Expr::Sort { level: la, .. }, Expr::Sort { level: lb, .. }) => self.level_eq(la, lb),
            (Expr::Const { name: na, levels: ua, .. }, Expr::Const { name: nb, levels: ub, .. }) => {
                self.name_eq(na, nb) && self.levels_eq(ua, ub)
            }
            (Expr::App { fun: fa, arg: aa, .. }, Expr::App { fun: fb, arg: ab, .. }) => {
                self.expr_eq(fa, fb) && self.expr_eq(aa, ab)
            }
            (
                Expr::Proj { ty_name: ta, idx: ia, structure: sta, .. },
                Expr::Proj { ty_name: tb, idx: ib, structure: stb, .. },
            ) => ia == ib && self.name_eq(ta, tb) && self.expr_eq(sta, stb),
            (
                Expr::Local { binder_name: bna, binder_style: bsa, binder_type: bta, id: bia, .. },
                Expr::Local { binder_name: bnb, binder_style: bsb, binder_type: btb, id: bib, .. },
            ) => {
                bia == bib
                    && (!self.compare_binder_info || bsa == bsb)
                    && (!self.compare_binder_info || self.name_eq(bna, bnb))
                    && self.expr_eq(bta, btb)
            }
            (
                Expr::Pi { binder_name: bna, binder_style: bsa, binder_type: bta, body: bda, .. },
                Expr::Pi { binder_name: bnb, binder_style: bsb, binder_type: btb, body: bdb, .. },
            )
            | (
                Expr::Lambda { binder_name: bna, binder_style: bsa, binder_type: bta, body: bda, .. },
                Expr::Lambda { binder_name: bnb, binder_style: bsb, binder_type: btb, body: bdb, .. },
            ) => {
                (!self.compare_binder_info || bsa == bsb)
                    && (!self.compare_binder_info || self.name_eq(bna, bnb))
                    && self.expr_eq(bta, btb)
                    && self.expr_eq(bda, bdb)
            }
            (
                Expr::Let { binder_name: bna, binder_type: bta, val: va, body: bda, nondep: nda, .. },
                Expr::Let { binder_name: bnb, binder_type: btb, val: vb, body: bdb, nondep: ndb, .. },
            ) => {
                nda == ndb
                    && (!self.compare_binder_info || self.name_eq(bna, bnb))
                    && self.expr_eq(bta, btb)
                    && self.expr_eq(va, vb)
                    && self.expr_eq(bda, bdb)
            }
            _ => false,
        };

        if ok {
            self.cache.insert((ea, eb));
        }
        ok
    }

    fn declar_info_eq(&mut self, ia: &DeclarInfo<'a>, ib: &DeclarInfo<'b>) -> bool {
        self.name_eq(ia.name, ib.name) && self.levels_eq(ia.uparams, ib.uparams) && self.expr_eq(ia.ty, ib.ty)
    }

    fn declar_eq(&mut self, da: &Declar<'a>, db: &Declar<'b>) -> bool {
        use Declar::*;

        match (da, db) {
            (Axiom { info: ia }, Axiom { info: ib }) | (Quot { info: ia }, Quot { info: ib }) => {
                self.declar_info_eq(ia, ib)
            }
            (Theorem { val: va, info: ia }, Theorem { val: vb, info: ib })
            | (Opaque { val: va, info: ia }, Opaque { val: vb, info: ib }) => {
                self.expr_eq(*va, *vb) && self.declar_info_eq(ia, ib)
            }
            (Definition { val: va, hint: ha, info: ia }, Definition { val: vb, hint: hb, info: ib }) => {
                ha == hb && self.expr_eq(*va, *vb) && self.declar_info_eq(ia, ib)
            }
            (Inductive(da), Inductive(db)) => {
                self.declar_info_eq(&da.info, &db.info)
                    && da.is_recursive == db.is_recursive
                    && da.is_nested == db.is_nested
                    && da.num_params == db.num_params
                    && da.num_indices == db.num_indices
                    && self.names_eq(&da.all_ind_names, &db.all_ind_names)
                    && self.names_eq(&da.all_ctor_names, &db.all_ctor_names)
            }
            (Constructor(da), Constructor(db)) => {
                self.declar_info_eq(&da.info, &db.info)
                    && self.name_eq(da.inductive_name, db.inductive_name)
                    && da.ctor_idx == db.ctor_idx
                    && da.num_params == db.num_params
                    && da.num_fields == db.num_fields
            }
            (Recursor(da), Recursor(db)) => {
                self.declar_info_eq(&da.info, &db.info)
                    && self.names_eq(&da.all_inductives, &db.all_inductives)
                    && da.num_params == db.num_params
                    && da.num_indices == db.num_indices
                    && da.num_motives == db.num_motives
                    && da.num_minors == db.num_minors
                    && da.rec_rules.len() == db.rec_rules.len()
                    && da.rec_rules.iter().zip(db.rec_rules.iter()).all(|(ra, rb)| {
                        self.name_eq(ra.ctor_name, rb.ctor_name)
                            && ra.ctor_telescope_size_wo_params == rb.ctor_telescope_size_wo_params
                            && self.expr_eq(ra.val, rb.val)
                    })
                    && da.is_k == db.is_k
            }
            _ => false,
        }
    }
}

/// Similar to Lean kernel's `lean_expr_eqv`, i.e. equality up to alpha-renaming.
/// This is Lean's instance for `BEq Lean.Expr`.
pub fn expr_eqv<'a, 'b>(fa: &'a ExportFile<'a>, ea: ExprPtr<'a>, fb: &'b ExportFile<'b>, eb: ExprPtr<'b>) -> bool {
    let mut ctx = EqCtx::new(fa, fb, false);
    ctx.expr_eq(ea, eb)
}

/// Similar to Lean kernel's `lean_expr_equal`.
pub fn expr_equal<'a, 'b>(fa: &'a ExportFile<'a>, ea: ExprPtr<'a>, fb: &'b ExportFile<'b>, eb: ExprPtr<'b>) -> bool {
    let mut ctx = EqCtx::new(fa, fb, true);
    ctx.expr_eq(ea, eb)
}

/// Mirror of `deriving BEq for Lean.ConstantVal`.
pub fn declar_info_equal<'a, 'b>(
    fa: &'a ExportFile<'a>,
    ia: &DeclarInfo<'a>,
    fb: &'b ExportFile<'b>,
    ib: &DeclarInfo<'b>,
) -> bool {
    let mut ctx = EqCtx::new(fa, fb, false);
    ctx.declar_info_eq(ia, ib)
}

/// Mirror of `deriving BEq for Lean.ConstantInfo`,
/// but only over the fields nanoda retains (e.g. `all`, `safety` ignored for defs).
pub fn declar_equal<'a, 'b>(fa: &'a ExportFile<'a>, da: &Declar<'a>, fb: &'b ExportFile<'b>, db: &Declar<'b>) -> bool {
    let mut ctx = EqCtx::new(fa, fb, false);
    ctx.declar_eq(da, db)
}
