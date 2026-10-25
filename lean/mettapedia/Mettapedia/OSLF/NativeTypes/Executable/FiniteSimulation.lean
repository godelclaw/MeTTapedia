import Mettapedia.OSLF.NativeTypes.Executable.Finite
import Mettapedia.OSLF.NativeTypes.Semantics.ModalSimulation

/-!
# Native queries through a finite simulation

A span map into a finite span need not lift anything, and the finite checker still decides two
fragments for the source, each in one direction:
- a formula without negation and boxes is refuted at a source state exactly when it fails at the
  state's image (`refuteSource_negative_iff`); the answer is never positive
  (`refuteSource_not_positive`);
- a formula without negation and diamonds is proved at a source state exactly when it holds at the
  state's image (`proveSource_positive_iff`); the answer is never negative (`proveSource_not_negative`).

With lifting, `checkSource` decides every positive formula both ways.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.Finite

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Reference.Core (Outcome)

universe u v e f
variable {State : Type u} {Source : Type v}
variable {span : ReductionSpan.{u, e} State} [Fintype State] [DecidableEq State]

/-- Refute a formula without negation and boxes at a source state by checking it at the image. -/
def refuteSource {original : ReductionSpan.{v, f} Source}
    (table : FiniteGraph.Table span) (observation : SpanMap original span)
    {n : Nat} (formula : Formula Traversal n) (existential : formula.existential = true)
    (environment : FiniteMuCalculus.Environment State n) (budget : Nat) (source : Source) :
    Outcome (satisfies (transitionSystem original)
      (pullEnvironment observation.states environment.meaning) formula source) :=
  match FiniteMuCalculus.check (model table) formula (fixedPointsPositive_of_existential formula existential)
      environment budget (observation.states source) with
  | .refuted fails =>
      .refuted (not_satisfies_of_spanMap observation formula existential environment.meaning source fails)
  | _ => .unknown

/-- **A refutation never proves the formula.** -/
theorem refuteSource_not_positive {original : ReductionSpan.{v, f} Source}
    (table : FiniteGraph.Table span) (observation : SpanMap original span)
    {n : Nat} (formula : Formula Traversal n) (existential : formula.existential = true)
    (environment : FiniteMuCalculus.Environment State n) (budget : Nat) (source : Source) :
    (refuteSource table observation formula existential environment budget source).answer ≠ some true := by
  unfold refuteSource
  split <;> simp [Outcome.answer]

/-- **The refutation is the finite answer**: with enough budget, the source is refuted exactly when the
formula fails at its image. -/
theorem refuteSource_negative_iff {original : ReductionSpan.{v, f} Source}
    (table : FiniteGraph.Table span) (observation : SpanMap original span)
    {n : Nat} (formula : Formula Traversal n) (existential : formula.existential = true)
    (environment : FiniteMuCalculus.Environment State n) (budget : Nat) (source : Source)
    (enough : FiniteMuCalculus.requiredBudget (State := State) formula ≤ budget) :
    (refuteSource table observation formula existential environment budget source).answer = some false ↔
      ¬ satisfies (transitionSystem span) environment.meaning formula (observation.states source) := by
  rw [← FiniteMuCalculus.check_negative_iff (model table) formula
    (fixedPointsPositive_of_existential formula existential) environment budget (observation.states source) enough]
  unfold refuteSource
  generalize FiniteMuCalculus.check (model table) formula (fixedPointsPositive_of_existential formula existential)
    environment budget (observation.states source) = result
  cases result <;> simp [Outcome.answer]

/-- Prove a formula without negation and diamonds at a source state by checking it at the image. -/
def proveSource {original : ReductionSpan.{v, f} Source}
    (table : FiniteGraph.Table span) (observation : SpanMap original span)
    {n : Nat} (formula : Formula Traversal n) (universal : formula.universal = true)
    (environment : FiniteMuCalculus.Environment State n) (budget : Nat) (source : Source) :
    Outcome (satisfies (transitionSystem original)
      (pullEnvironment observation.states environment.meaning) formula source) :=
  match FiniteMuCalculus.check (model table) formula (fixedPointsPositive_of_universal formula universal)
      environment budget (observation.states source) with
  | .proved holds =>
      .proved (satisfies_pull_of_spanMap observation formula universal environment.meaning source holds)
  | _ => .unknown

/-- **A proof never refutes the formula.** -/
theorem proveSource_not_negative {original : ReductionSpan.{v, f} Source}
    (table : FiniteGraph.Table span) (observation : SpanMap original span)
    {n : Nat} (formula : Formula Traversal n) (universal : formula.universal = true)
    (environment : FiniteMuCalculus.Environment State n) (budget : Nat) (source : Source) :
    (proveSource table observation formula universal environment budget source).answer ≠ some false := by
  unfold proveSource
  split <;> simp [Outcome.answer]

/-- **The proof is the finite answer**: with enough budget, the source is proved exactly when the
formula holds at its image. -/
theorem proveSource_positive_iff {original : ReductionSpan.{v, f} Source}
    (table : FiniteGraph.Table span) (observation : SpanMap original span)
    {n : Nat} (formula : Formula Traversal n) (universal : formula.universal = true)
    (environment : FiniteMuCalculus.Environment State n) (budget : Nat) (source : Source)
    (enough : FiniteMuCalculus.requiredBudget (State := State) formula ≤ budget) :
    (proveSource table observation formula universal environment budget source).answer = some true ↔
      satisfies (transitionSystem span) environment.meaning formula (observation.states source) := by
  rw [← FiniteMuCalculus.check_positive_iff (model table) formula
    (fixedPointsPositive_of_universal formula universal) environment budget (observation.states source) enough]
  unfold proveSource
  generalize FiniteMuCalculus.check (model table) formula (fixedPointsPositive_of_universal formula universal)
    environment budget (observation.states source) = result
  cases result <;> simp [Outcome.answer]

end Mettapedia.OSLF.NativeTypes.Executable.Finite
