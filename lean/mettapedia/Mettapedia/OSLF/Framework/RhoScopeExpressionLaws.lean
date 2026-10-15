import Mettapedia.OSLF.Framework.RhoScopeExpression

/-!
# Scope binder laws for the sorted quotient interpretation

The actual least-fixed-point interpretation unfolds and is below every
pre-fixed point of its independently interpreted body. Positional scope
variables obey their binder depth: changing an environment beyond that depth
preserves a closed expression's entire predicate. In particular, closed
scope expressions do not depend on an arbitrary external scope environment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeExpressionLaws

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationGeneratedScope RhoScopeExpression

universe u

theorem mu_unfold {Atom : Type u} {context : Ctx sig}
    (atoms : Atom → Process context → Prop) (body : Expression Atom Srt.nm)
    (env : RhoScopeExpression.Environment context) :
    denote atoms body (push (denote atoms (.mu body) env) env) =
      denote atoms (.mu body) env :=
  OrderHom.map_lfp ((denote atoms body).comp (pushNames env))

theorem mu_induction {Atom : Type u} {context : Ctx sig}
    (atoms : Atom → Process context → Prop) (body : Expression Atom Srt.nm)
    (env : RhoScopeExpression.Environment context) (invariant : NamePredicate context)
    (closed : denote atoms body (push invariant env) ≤ invariant) :
    denote atoms (.mu body) env ≤ invariant :=
  ((denote atoms body).comp (pushNames env)).lfp_le closed

theorem environment_congr {Atom : Type u} {context : Ctx sig}
    (atoms : Atom → Process context → Prop) {sort : Srt} (expression : Expression Atom sort) :
    ∀ (depth : Nat) (first second : RhoScopeExpression.Environment context),
      expression.closedAt depth = true →
      (∀ index, index < depth → first index = second index) →
      denote atoms expression first = denote atoms expression second := by
  induction expression with
  | atom label => intro depth first second _ _; rfl
  | var index =>
      intro depth first second closed same
      exact same index (of_decide_eq_true closed)
  | or firstExpression secondExpression firstIH secondIH =>
      intro depth first second closed same
      have both := Bool.and_eq_true_iff.mp closed
      have left := firstIH depth first second both.1 same
      have right := secondIH depth first second both.2 same
      funext value
      change (denote atoms firstExpression first value ∨ denote atoms secondExpression first value) =
        (denote atoms firstExpression second value ∨ denote atoms secondExpression second value)
      rw [left, right]
  | quote expression ih =>
      intro depth first second closed same
      have equal := ih depth first second closed same
      funext name
      change (∃ process, denote atoms expression first process ∧ quote process = name) =
        (∃ process, denote atoms expression second process ∧ quote process = name)
      rw [equal]
  | drop expression ih =>
      intro depth first second closed same
      have equal := ih depth first second closed same
      funext process
      change (∃ name, denote atoms expression first name ∧ drop name = process) =
        (∃ name, denote atoms expression second name ∧ drop name = process)
      rw [equal]
  | par firstExpression secondExpression firstIH secondIH =>
      intro depth first second closed same
      have both := Bool.and_eq_true_iff.mp closed
      have left := firstIH depth first second both.1 same
      have right := secondIH depth first second both.2 same
      funext value
      change (∃ firstProcess secondProcess,
        denote atoms firstExpression first firstProcess ∧
        denote atoms secondExpression first secondProcess ∧ join firstProcess secondProcess = value) =
        (∃ firstProcess secondProcess,
        denote atoms firstExpression second firstProcess ∧
        denote atoms secondExpression second secondProcess ∧ join firstProcess secondProcess = value)
      rw [left, right]
  | mu body ih =>
      intro depth first second closed same
      change ((denote atoms body).comp (pushNames first)).lfp =
        ((denote atoms body).comp (pushNames second)).lfp
      congr 1
      apply OrderHom.ext
      funext names
      apply ih (depth + 1) (push names first) (push names second) closed
      intro index small
      cases index with
      | zero => rfl
      | succ index => exact same index (Nat.lt_of_succ_lt_succ small)

theorem closed_environment_independent {Atom : Type u} {context : Ctx sig}
    (atoms : Atom → Process context → Prop) {sort : Srt} (expression : Expression Atom sort)
    (closed : expression.closedAt 0 = true)
    (first second : RhoScopeExpression.Environment context) :
    denote atoms expression first = denote atoms expression second :=
  environment_congr atoms expression 0 first second closed
    (fun _ impossible => False.elim (Nat.not_lt_zero _ impossible))

end Mettapedia.OSLF.Framework.RhoScopeExpressionLaws
