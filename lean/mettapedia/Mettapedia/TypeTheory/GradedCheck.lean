import Mettapedia.TypeTheory.Authority

/-!
# A checking service under a budget: the contract of a graded check

A graded check runs an authority's judgment at a budget and returns one of the four
outcomes of `AuthorityTheory.Outcome`: established evidence, a checked refutation, a stable
boundary of the checker's fragment, or an exhausted budget. Its one law is monotonicity in
the budget, in the sense of `Outcome.BudgetRefines`: only an exhausted run may change its
outcome when the budget grows. Soundness of the two decided outcomes is carried by the
authority's evidence types.

* **Decided outcomes persist** (`established_persists`, `refuted_persists`,
  `outside_persists`). They are sound because their payloads are the authority's evidence
  and obstructions (`Authority.evidenceSound`, `Authority.obstructionSound`).
* **A Boolean reading of refutation must be stable** (`refutation_reading_stable`). If
  `false` is to mean "a checked refutation was found", a reading that answers `false` at a
  budget answers `false` at every larger budget.
* **So a recognizer that turns from `false` to `true` as its budget grows does not read
  refutation of any graded check** (`no_refutation_reading_of_flip`). Its `false` reads
  "nothing found within this budget", which is the exhausted outcome. The Megalodon
  definition search in `Languages.Megalodon.DirectedSearchGradedCheck` is the concrete case.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.GradedChecking

open AuthorityTheory

universe u v w x y

set_option linter.checkUnivs false in
/-- A graded check: a run at every budget, monotone in the budget. -/
structure GradedCheck {Judgment : Type u} (authority : Authority.{u, v, w} Judgment)
    (Boundary : Type x) (Incomplete : Type y) where
  run : ℕ → (judgment : Judgment) → AuthorizedOutcome authority Boundary Incomplete judgment
  mono : ∀ (judgment : Judgment) {small large : ℕ}, small ≤ large →
    Outcome.BudgetRefines (run small judgment) (run large judgment)

namespace GradedCheck

variable {Judgment : Type u} {authority : Authority.{u, v, w} Judgment}
  {Boundary : Type x} {Incomplete : Type y}
  (check : GradedCheck authority Boundary Incomplete)

/-- **Established evidence persists at larger budgets.** -/
theorem established_persists {small large : ℕ} (le : small ≤ large) {judgment : Judgment}
    {evidence : authority.Evidence judgment}
    (ran : check.run small judgment = .established evidence) :
    ∃ later, check.run large judgment = .established later := by
  have refines := check.mono judgment le
  rw [ran] at refines
  generalize check.run large judgment = outcome at refines ⊢
  cases refines with
  | established _ later => exact ⟨later, rfl⟩

/-- **A checked refutation persists at larger budgets.** -/
theorem refuted_persists {small large : ℕ} (le : small ≤ large) {judgment : Judgment}
    {obstruction : authority.Obstruction judgment}
    (ran : check.run small judgment = .refuted obstruction) :
    ∃ later, check.run large judgment = .refuted later := by
  have refines := check.mono judgment le
  rw [ran] at refines
  generalize check.run large judgment = outcome at refines ⊢
  cases refines with
  | refuted _ later => exact ⟨later, rfl⟩

/-- **A fragment boundary is stable under larger budgets.** -/
theorem outside_persists {small large : ℕ} (le : small ≤ large) {judgment : Judgment}
    {reason : Boundary} (ran : check.run small judgment = .outsideFragment reason) :
    check.run large judgment = .outsideFragment reason := by
  have refines := check.mono judgment le
  rw [ran] at refines
  exact Outcome.budget_does_not_resolve_outside reason _ refines

/-- **A Boolean reading of refutation is stable under larger budgets.** -/
theorem refutation_reading_stable (read : ℕ → Judgment → Bool)
    (reads : ∀ budget judgment,
      read budget judgment = false ↔ ∃ obstruction, check.run budget judgment = .refuted obstruction)
    {small large : ℕ} (le : small ≤ large) {judgment : Judgment}
    (answered : read small judgment = false) : read large judgment = false := by
  obtain ⟨obstruction, ran⟩ := (reads small judgment).mp answered
  exact (reads large judgment).mpr (check.refuted_persists le ran)

end GradedCheck

/-- **A recognizer that turns from `false` to `true` reads refutation of no graded check.** -/
theorem no_refutation_reading_of_flip {Judgment : Type u} {authority : Authority.{u, v, w} Judgment}
    {Boundary : Type x} {Incomplete : Type y} (read : ℕ → Judgment → Bool) {judgment : Judgment}
    {small large : ℕ} (le : small ≤ large) (falseAtSmall : read small judgment = false)
    (trueAtLarge : read large judgment = true) :
    ¬ ∃ check : GradedCheck authority Boundary Incomplete, ∀ budget judgment,
      read budget judgment = false ↔
        ∃ obstruction, check.run budget judgment = .refuted obstruction := by
  rintro ⟨check, reads⟩
  have stays := check.refutation_reading_stable read reads le falseAtSmall
  rw [trueAtLarge] at stays
  cases stays

/-! ## Axiom audit -/

#print axioms GradedCheck.established_persists
#print axioms GradedCheck.refuted_persists
#print axioms GradedCheck.outside_persists
#print axioms GradedCheck.refutation_reading_stable
#print axioms no_refutation_reading_of_flip

end Mettapedia.TypeTheory.GradedChecking
