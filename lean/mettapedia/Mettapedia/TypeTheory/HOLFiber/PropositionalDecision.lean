import Mettapedia.Logic.HOL.PropositionalSlice
import Mettapedia.GSLT.LanguageDef.KernelAuthority

/-!
# A decidable bubble of the HOL fiber: the quantifier-free `bool` fragment

On propositional formulas, HOL with the excluded-middle schema proves exactly
the classical tautologies (`PropositionalSlice.provable_em_iff_cl`). A
tautology is decided by evaluating the formula at every assignment of its
atoms, so theoremhood of the fragment is decided by a terminating Boolean
computation, `tautCheck`:

* `tautCheck_iff`: `tautCheck φ = true` exactly when `φ` is a classical
  tautology;
* `provable_em_iff_tautCheck`: exactly when HOL with excluded middle proves the
  image of `φ`;
* `satisfiable_iff`: a formula has a satisfying assignment exactly when the
  check rejects its negation (the SAT form of the same decision).

`decisionKernel` packages the check as a direct decision kernel for HOL
theoremhood on the fragment, and `decisionKernel_authority` is its exact
authority as a checker with trivial certificates.

The decision is for the propositional image only: atoms are propositional
constants, and no quantifier, base type or equation is in the fragment. It says
nothing about the full calculus, whose theoremhood is not decidable.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HOLFiber.PropositionalDecision

open LO LO.Propositional
open Mettapedia.Logic.HOL Mettapedia.Logic.HOL.PropositionalSlice
open ClosedTheorySet
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker

/-! ## Boolean evaluation -/

/-- Evaluation of a formula at a Boolean assignment. -/
def evalB (v : ℕ → Bool) : PropFormula → Bool
  | .atom a => v a
  | .falsum => false
  | .and φ ψ => evalB v φ && evalB v ψ
  | .or φ ψ => evalB v φ || evalB v ψ
  | .imp φ ψ => !evalB v φ || evalB v ψ

/-- Boolean evaluation computes the classical truth value. -/
theorem val_iff_evalB (v : ℕ → Bool) :
    ∀ φ : PropFormula,
      Formula.ClassicalSemantics.val (fun a => v a = true) φ ↔ evalB v φ = true
  | .atom a => Iff.rfl
  | .falsum => by simp [Formula.ClassicalSemantics.val, evalB]
  | .and φ ψ => by
      simp only [Formula.ClassicalSemantics.val, evalB, Bool.and_eq_true]
      exact and_congr (val_iff_evalB v φ) (val_iff_evalB v ψ)
  | .or φ ψ => by
      simp only [Formula.ClassicalSemantics.val, evalB, Bool.or_eq_true]
      exact or_congr (val_iff_evalB v φ) (val_iff_evalB v ψ)
  | .imp φ ψ => by
      simp only [Formula.ClassicalSemantics.val, evalB, Bool.or_eq_true, Bool.not_eq_true']
      rw [val_iff_evalB v φ, val_iff_evalB v ψ]
      cases evalB v φ <;> simp

/-- Classical truth respects pointwise equivalence of valuations. -/
theorem val_congr {v w : ℕ → Prop} (same : ∀ a, v a ↔ w a) :
    ∀ φ : PropFormula,
      Formula.ClassicalSemantics.val v φ ↔ Formula.ClassicalSemantics.val w φ
  | .atom a => same a
  | .falsum => Iff.rfl
  | .and φ ψ => and_congr (val_congr same φ) (val_congr same ψ)
  | .or φ ψ => or_congr (val_congr same φ) (val_congr same ψ)
  | .imp φ ψ => imp_congr (val_congr same φ) (val_congr same ψ)

/-! ## Atoms and assignments -/

/-- The atoms of a formula, with repetitions. -/
def atoms : PropFormula → List ℕ
  | .atom a => [a]
  | .falsum => []
  | .and φ ψ => atoms φ ++ atoms ψ
  | .or φ ψ => atoms φ ++ atoms ψ
  | .imp φ ψ => atoms φ ++ atoms ψ

/-- Evaluation reads only the atoms of the formula. -/
theorem evalB_congr {v w : ℕ → Bool} :
    ∀ φ : PropFormula, (∀ a ∈ atoms φ, v a = w a) → evalB v φ = evalB w φ
  | .atom a, agree => agree a (by simp [atoms])
  | .falsum, _ => rfl
  | .and φ ψ, agree => by
      simp only [evalB]
      rw [evalB_congr φ fun a h => agree a (by simp [atoms, h]),
        evalB_congr ψ fun a h => agree a (by simp [atoms, h])]
  | .or φ ψ, agree => by
      simp only [evalB]
      rw [evalB_congr φ fun a h => agree a (by simp [atoms, h]),
        evalB_congr ψ fun a h => agree a (by simp [atoms, h])]
  | .imp φ ψ, agree => by
      simp only [evalB]
      rw [evalB_congr φ fun a h => agree a (by simp [atoms, h]),
        evalB_congr ψ fun a h => agree a (by simp [atoms, h])]

/-- Every assignment of the listed atoms, each extended by `false`. -/
def assignments : List ℕ → List (ℕ → Bool)
  | [] => [fun _ => false]
  | a :: rest =>
      (assignments rest).flatMap fun v => [Function.update v a false, Function.update v a true]

/-- Every valuation agrees, on the listed atoms, with one of the assignments. -/
theorem exists_assignment (v : ℕ → Bool) :
    ∀ listed : List ℕ, ∃ w ∈ assignments listed, ∀ a ∈ listed, w a = v a
  | [] => ⟨fun _ => false, by simp [assignments], by simp⟩
  | a :: rest => by
      obtain ⟨w, member, agree⟩ := exists_assignment v rest
      refine ⟨Function.update w a (v a), ?_, ?_⟩
      · simp only [assignments, List.mem_flatMap]
        refine ⟨w, member, ?_⟩
        cases v a <;> simp
      · intro b listed
        by_cases same : b = a
        · subst same
          simp
        · rw [Function.update_of_ne same]
          exact agree b (by simpa [same] using listed)

/-! ## The check -/

/-- Evaluate the formula at every assignment of its atoms. -/
def tautCheck (φ : PropFormula) : Bool :=
  (assignments (atoms φ)).all fun v => evalB v φ

/-- **The check decides classical validity.** -/
theorem tautCheck_iff (φ : PropFormula) : tautCheck φ = true ↔ φ.Tautology := by
  constructor
  · intro accepted v
    classical
    let b : ℕ → Bool := fun a => decide (v a)
    obtain ⟨w, member, agree⟩ := exists_assignment b (atoms φ)
    have atW : evalB w φ = true := List.all_eq_true.mp accepted w member
    have atB : evalB b φ = true := by rw [← evalB_congr φ agree]; exact atW
    have truth := (val_iff_evalB b φ).mpr atB
    refine Formula.ClassicalSemantics.models_iff_val.mpr ((val_congr ?_ φ).mp truth)
    intro a
    simp [b]
  · intro valid
    refine List.all_eq_true.mpr fun w _ => ?_
    exact (val_iff_evalB w φ).mp (Formula.ClassicalSemantics.models_iff_val.mp (valid _))

/-- **Theoremhood of the bubble is decided.** HOL with the excluded-middle
schema proves the image of a propositional formula exactly when the check
accepts it. -/
theorem provable_em_iff_tautCheck (φ : PropFormula) :
    Provable (EMSchema Atom) (embedP φ) ↔ tautCheck φ = true :=
  provable_em_iff_cl.trans (Cl.iff_provable_tautology.trans (tautCheck_iff φ).symm)

instance decidableProvable : DecidablePred fun φ : PropFormula =>
    Provable (EMSchema Atom) (embedP φ) :=
  fun φ => decidable_of_iff _ (provable_em_iff_tautCheck φ).symm

/-- The SAT form: a formula is satisfiable exactly when its negation is not a
theorem of the bubble. -/
theorem satisfiable_iff (φ : PropFormula) :
    (∃ v : ℕ → Prop, Formula.ClassicalSemantics.val v φ) ↔ tautCheck (∼φ) = false := by
  rw [← Bool.not_eq_true, tautCheck_iff]
  constructor
  · rintro ⟨v, holds⟩ valid
    exact (Formula.ClassicalSemantics.models_iff_val.mp (valid v)) holds
  · intro notValid
    by_contra none
    exact notValid fun v => Formula.ClassicalSemantics.models_iff_val.mpr fun h => none ⟨v, h⟩

/-- The check as a direct decision kernel for HOL theoremhood on the bubble. -/
def decisionKernel : DecisionKernel PropFormula fun φ => Provable (EMSchema Atom) (embedP φ) where
  decide := tautCheck
  correct φ := (provable_em_iff_tautCheck φ).symm

/-- As a checker with trivial certificates it is an exact authority. -/
theorem decisionKernel_authority :
    decisionKernel.toChecker.Authority fun φ => Provable (EMSchema Atom) (embedP φ) :=
  decisionKernel.authority

/-! ## Controls -/

theorem excludedMiddle_accepted : tautCheck (.atom 0 ⋎ ∼(.atom 0)) = true := by decide

theorem peirce_accepted : tautCheck peirce = true := by decide

theorem atom_rejected : tautCheck (.atom 0) = false := by decide

/-- The decision agrees with the existing separation: excluded middle is a
theorem of the bubble with the schema. -/
theorem excludedMiddle_provable :
    Provable (EMSchema Atom) (embedP (.atom 0 ⋎ ∼(.atom 0))) :=
  (provable_em_iff_tautCheck _).mpr excludedMiddle_accepted

/-- An atom is not a theorem of the bubble. -/
theorem atom_not_provable : ¬ Provable (EMSchema Atom) (embedP (.atom 0)) := by
  rw [provable_em_iff_tautCheck]
  decide

/-! ## Axiom audit -/

#print axioms tautCheck_iff
#print axioms provable_em_iff_tautCheck
#print axioms satisfiable_iff
#print axioms decisionKernel_authority
#print axioms atom_not_provable

end Mettapedia.TypeTheory.HOLFiber.PropositionalDecision
