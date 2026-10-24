import Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
import Mettapedia.Logic.ModalMuCalculusSimulation
import Mettapedia.OSLF.Framework.BackwardSearch

/-!
# Native formulas along maps of spans

A map that carries every step of one reduction span to a step of another, in both traversals,
preserves the transitions of their transition systems; every span map does
(`preservesTransitions_of_spanMap`). With the pulled-back environment, and nested fixed points included:
- each formula of the modal μ-calculus without negation and boxes holds at the image of every state
  where it holds (`satisfies_of_spanMap`);
- each formula without negation and diamonds holds at every state where it holds at the image
  (`satisfies_pull_of_spanMap`).

No lifting is needed. Each is one direction of `satisfies_pullback`, for its own fragment; that theorem
is an equivalence for every positive formula and needs lifting for the traversals the formula uses. Both
fragments pass the positivity gate of the fixed-point checkers (`fixedPointsPositive_of_existential`,
`fixedPointsPositive_of_universal`).

`reachFormula`, `μ X. goal ∨ ◇ X`, is reachability of its free predicate (`satisfies_reach_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.BackwardSearch (Reaches)
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary

universe u v e f w
variable {X : Type u} {Y : Type v}

/-! ## Existential formulas pass the positivity gate -/

theorem isPositiveIn_of_existential {Action : Type w} :
    ∀ {n : ℕ} (formula : Formula Action n), formula.existential = true →
      ∀ index : Fin n, formula.isPositiveIn index true = true
  | _, .tt, _, _ => rfl
  | _, .ff, _, _ => rfl
  | _, .neg _, existential, _ => by simp [Formula.existential] at existential
  | _, .box _ _, existential, _ => by simp [Formula.existential] at existential
  | _, .conj first second, existential, index => by
    simp only [Formula.existential, Bool.and_eq_true] at existential
    simp [Formula.isPositiveIn, isPositiveIn_of_existential first existential.1 index,
      isPositiveIn_of_existential second existential.2 index]
  | _, .disj first second, existential, index => by
    simp only [Formula.existential, Bool.and_eq_true] at existential
    simp [Formula.isPositiveIn, isPositiveIn_of_existential first existential.1 index,
      isPositiveIn_of_existential second existential.2 index]
  | _, .diamond _ body, existential, index => by
    simpa [Formula.isPositiveIn] using isPositiveIn_of_existential body existential index
  | _, .mu body, existential, index => by
    simpa [Formula.isPositiveIn] using isPositiveIn_of_existential body existential index.succ
  | _, .nu body, existential, index => by
    simpa [Formula.isPositiveIn] using isPositiveIn_of_existential body existential index.succ
  | _, .var _, _, _ => by simp [Formula.isPositiveIn]

/-- A formula without negation and boxes has positive fixed-point bodies. -/
theorem fixedPointsPositive_of_existential {Action : Type w} :
    ∀ {n : ℕ} (formula : Formula Action n), formula.existential = true → fixedPointsPositive formula = true
  | _, .tt, _ => rfl
  | _, .ff, _ => rfl
  | _, .var _, _ => rfl
  | _, .neg _, existential => by simp [Formula.existential] at existential
  | _, .box _ _, existential => by simp [Formula.existential] at existential
  | _, .conj first second, existential => by
    simp only [Formula.existential, Bool.and_eq_true] at existential
    simp [fixedPointsPositive, fixedPointsPositive_of_existential first existential.1,
      fixedPointsPositive_of_existential second existential.2]
  | _, .disj first second, existential => by
    simp only [Formula.existential, Bool.and_eq_true] at existential
    simp [fixedPointsPositive, fixedPointsPositive_of_existential first existential.1,
      fixedPointsPositive_of_existential second existential.2]
  | _, .diamond _ body, existential => by
    simpa [fixedPointsPositive] using fixedPointsPositive_of_existential body existential
  | _, .mu body, existential => by
    simp [fixedPointsPositive, Formula.isPositive, isPositiveIn_of_existential body existential 0,
      fixedPointsPositive_of_existential body existential]
  | _, .nu body, existential => by
    simp [fixedPointsPositive, Formula.isPositive, isPositiveIn_of_existential body existential 0,
      fixedPointsPositive_of_existential body existential]

theorem isPositiveIn_of_universal {Action : Type w} :
    ∀ {n : ℕ} (formula : Formula Action n), formula.universal = true →
      ∀ index : Fin n, formula.isPositiveIn index true = true
  | _, .tt, _, _ => rfl
  | _, .ff, _, _ => rfl
  | _, .neg _, universal, _ => by simp [Formula.universal] at universal
  | _, .diamond _ _, universal, _ => by simp [Formula.universal] at universal
  | _, .conj first second, universal, index => by
    simp only [Formula.universal, Bool.and_eq_true] at universal
    simp [Formula.isPositiveIn, isPositiveIn_of_universal first universal.1 index,
      isPositiveIn_of_universal second universal.2 index]
  | _, .disj first second, universal, index => by
    simp only [Formula.universal, Bool.and_eq_true] at universal
    simp [Formula.isPositiveIn, isPositiveIn_of_universal first universal.1 index,
      isPositiveIn_of_universal second universal.2 index]
  | _, .box _ body, universal, index => by
    simpa [Formula.isPositiveIn] using isPositiveIn_of_universal body universal index
  | _, .mu body, universal, index => by
    simpa [Formula.isPositiveIn] using isPositiveIn_of_universal body universal index.succ
  | _, .nu body, universal, index => by
    simpa [Formula.isPositiveIn] using isPositiveIn_of_universal body universal index.succ
  | _, .var _, _, _ => by simp [Formula.isPositiveIn]

/-- A formula without negation and diamonds has positive fixed-point bodies. -/
theorem fixedPointsPositive_of_universal {Action : Type w} :
    ∀ {n : ℕ} (formula : Formula Action n), formula.universal = true → fixedPointsPositive formula = true
  | _, .tt, _ => rfl
  | _, .ff, _ => rfl
  | _, .var _, _ => rfl
  | _, .neg _, universal => by simp [Formula.universal] at universal
  | _, .diamond _ _, universal => by simp [Formula.universal] at universal
  | _, .conj first second, universal => by
    simp only [Formula.universal, Bool.and_eq_true] at universal
    simp [fixedPointsPositive, fixedPointsPositive_of_universal first universal.1,
      fixedPointsPositive_of_universal second universal.2]
  | _, .disj first second, universal => by
    simp only [Formula.universal, Bool.and_eq_true] at universal
    simp [fixedPointsPositive, fixedPointsPositive_of_universal first universal.1,
      fixedPointsPositive_of_universal second universal.2]
  | _, .box _ body, universal => by
    simpa [fixedPointsPositive] using fixedPointsPositive_of_universal body universal
  | _, .mu body, universal => by
    simp [fixedPointsPositive, Formula.isPositive, isPositiveIn_of_universal body universal 0,
      fixedPointsPositive_of_universal body universal]
  | _, .nu body, universal => by
    simp [fixedPointsPositive, Formula.isPositive, isPositiveIn_of_universal body universal 0,
      fixedPointsPositive_of_universal body universal]

/-! ## Transfer along maps -/

variable {A : ReductionSpan.{u, e} X} {B : ReductionSpan.{v, f} Y}

/-- **A span map preserves the transitions of both traversals.** -/
theorem preservesTransitions_of_spanMap (observation : SpanMap A B) :
    PreservesTransitions (transitionSystem A) (transitionSystem B) observation.states :=
  fun _ direction _ step => transition_preserved observation direction step

/-- **Existential formulas hold at images**: along a map that preserves the transitions of both
traversals, a formula without negation and boxes that holds at a state, under the pulled-back
environment, holds at its image. -/
theorem satisfies_of_preserves_pull {observe : X → Y}
    (preserves : PreservesTransitions (transitionSystem A) (transitionSystem B) observe) {n : ℕ}
    (formula : Formula Traversal n) (existential : formula.existential = true) (environment : Env Y n)
    (source : X) (holds : satisfies (transitionSystem A) (pullEnvironment observe environment) formula source) :
    satisfies (transitionSystem B) environment formula (observe source) :=
  satisfies_of_preserves preserves formula existential (fun _ _ member => member) source holds

theorem satisfies_of_spanMap (observation : SpanMap A B) {n : ℕ} (formula : Formula Traversal n)
    (existential : formula.existential = true) (environment : Env Y n) (source : X)
    (holds : satisfies (transitionSystem A) (pullEnvironment observation.states environment) formula source) :
    satisfies (transitionSystem B) environment formula (observation.states source) :=
  satisfies_of_preserves_pull (preservesTransitions_of_spanMap observation) formula existential environment
    source holds

/-- **Refutations transfer back**: when an existential formula fails at the image of a state, it fails
at the state under the pulled-back environment. -/
theorem not_satisfies_of_spanMap (observation : SpanMap A B) {n : ℕ} (formula : Formula Traversal n)
    (existential : formula.existential = true) (environment : Env Y n) (source : X)
    (fails : ¬ satisfies (transitionSystem B) environment formula (observation.states source)) :
    ¬ satisfies (transitionSystem A) (pullEnvironment observation.states environment) formula source :=
  fun holds => fails (satisfies_of_spanMap observation formula existential environment source holds)

/-- **Universal formulas hold at states**: along a map that preserves the transitions of both
traversals, a formula without negation and diamonds that holds at the image of a state holds at the
state, under the pulled-back environment. -/
theorem satisfies_pull_of_spanMap (observation : SpanMap A B) {n : ℕ} (formula : Formula Traversal n)
    (universal : formula.universal = true) (environment : Env Y n) (source : X)
    (holds : satisfies (transitionSystem B) environment formula (observation.states source)) :
    satisfies (transitionSystem A) (pullEnvironment observation.states environment) formula source :=
  satisfies_of_preserves_universal (preservesTransitions_of_spanMap observation) formula universal
    (fun _ _ member => member) source holds

/-! ## Reachability -/

/-- `μ X. goal ∨ ◇ X`, with the goal as its free predicate. -/
def reachFormula : Formula Traversal 1 := .mu (.disj (.var 1) (.diamond .future (.var 0)))

theorem reachFormula_existential : reachFormula.existential = true := rfl

/-- **Reachability is the least fixed point of `goal ∨ ◇ X`.** -/
theorem satisfies_reach_iff (span : ReductionSpan.{u, e} X) (environment : Env X 1) (state : X) :
    satisfies (transitionSystem span) environment reachFormula state ↔
      Reaches span (· ∈ environment 0) state := by
  constructor
  · intro holds
    refine holds {other | Reaches span (· ∈ environment 0) other} fun other body => ?_
    rcases body with atGoal | ⟨next, ⟨event, rfl, rfl⟩, nextReaches⟩
    · exact Reaches.goal atGoal
    · exact Reaches.step event nextReaches
  · intro reaches closed closedHolds
    induction reaches with
    | goal atGoal => exact closedHolds _ (Or.inl atGoal)
    | step event _ ih => exact closedHolds _ (Or.inr ⟨_, ⟨event, rfl, rfl⟩, ih⟩)

end Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
