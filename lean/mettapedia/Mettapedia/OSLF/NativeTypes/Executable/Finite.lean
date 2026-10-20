import Mettapedia.OSLF.NativeTypes.Decision.FiniteGraph
import Mettapedia.OSLF.NativeTypes.Decision.FiniteMuCalculus
import Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
import Mettapedia.Logic.ModalMuCalculusBuchi

/-!
# Certified finite-model strategy for executable native queries

The caller supplies a complete finite span table, not merely the states visited
by a rooted search. Queries use the existing modal μ-calculus syntax and the
shared proof-carrying verdict. Positivity refusal, insufficient allowance, and
semantic refutation stay separate. A covered observation connects these finite
answers to an independently specified source span, which may be infinite.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.Finite

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Reference.Core (Outcome)

universe u v e f
variable {State : Type u} {Source : Type v}
variable {span : ReductionSpan.{u, e} State} [Fintype State] [DecidableEq State]

/-- Both traversals use the same independently checked table. Transposition
does not infer global predecessor coverage from a forward exploration. -/
def model (table : FiniteGraph.Table span) : FiniteMuCalculus.Model (transitionSystem span) where
  successors source direction := Finset.univ.filter fun target => (match direction with
    | .future => table.edge source target
    | .past => table.edge target source) = true
  successors_exact source direction target := by
    cases direction
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, transitionSystem] using table.exact source target
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, transitionSystem, and_comm] using table.exact target source

def check (table : FiniteGraph.Table span) {n : Nat} (formula : Formula Traversal n)
    (environment : FiniteMuCalculus.Environment State n) (budget : Nat) (state : State) :
    Option (Outcome (satisfies (transitionSystem span) environment.meaning formula state)) :=
  FiniteMuCalculus.check? (model table) formula environment budget state

theorem check_positive_iff (table : FiniteGraph.Table span) {n : Nat}
    (formula : Formula Traversal n) (positive : fixedPointsPositive formula = true)
    (environment : FiniteMuCalculus.Environment State n) (budget : Nat) (state : State)
    (enough : FiniteMuCalculus.requiredBudget (State := State) formula ≤ budget) :
    ((check table formula environment budget state).map Outcome.answer) = some (some true) ↔
      satisfies (transitionSystem span) environment.meaning formula state := by
  simpa only [check, FiniteMuCalculus.check?, positive, ↓reduceDIte, Option.map_some,
    Option.some.injEq] using
    FiniteMuCalculus.check_positive_iff (model table) formula positive environment budget state enough

theorem check_negative_iff (table : FiniteGraph.Table span) {n : Nat}
    (formula : Formula Traversal n) (positive : fixedPointsPositive formula = true)
    (environment : FiniteMuCalculus.Environment State n) (budget : Nat) (state : State)
    (enough : FiniteMuCalculus.requiredBudget (State := State) formula ≤ budget) :
    ((check table formula environment budget state).map Outcome.answer) = some (some false) ↔
      ¬ satisfies (transitionSystem span) environment.meaning formula state := by
  simpa only [check, FiniteMuCalculus.check?, positive, ↓reduceDIte, Option.map_some,
    Option.some.injEq] using
    FiniteMuCalculus.check_negative_iff (model table) formula positive environment budget state enough

/-- Source checking transports the finite result, rather than interpreting
the source request as an unrelated finite fixture. -/
def checkSource {original : ReductionSpan.{v, f} Source}
    (table : FiniteGraph.Table span) (observation : SpanMap original span)
    {n : Nat} (formula : Formula Traversal n)
    (coverage : CoversFormula observation formula)
    (environment : FiniteMuCalculus.Environment State n) (budget : Nat) (source : Source) :
    Option (Outcome (satisfies (transitionSystem original)
      (pullEnvironment observation.states environment.meaning) formula source)) :=
  if positive : fixedPointsPositive formula = true then
    some ((FiniteMuCalculus.check (model table) formula positive environment budget
      (observation.states source)).map
        (satisfies_pullback observation formula coverage positive environment.meaning source))
  else none

theorem checkSource_positive_iff {original : ReductionSpan.{v, f} Source}
    (table : FiniteGraph.Table span) (observation : SpanMap original span)
    {n : Nat} (formula : Formula Traversal n) (coverage : CoversFormula observation formula)
    (positive : fixedPointsPositive formula = true)
    (environment : FiniteMuCalculus.Environment State n) (budget : Nat) (source : Source)
    (enough : FiniteMuCalculus.requiredBudget (State := State) formula ≤ budget) :
    ((checkSource table observation formula coverage environment budget source).map Outcome.answer) =
        some (some true) ↔
      satisfies (transitionSystem original)
        (pullEnvironment observation.states environment.meaning) formula source := by
  have mapped (first second : Prop) (equivalent : first ↔ second) (result : Outcome first) :
      (result.map equivalent).answer = result.answer := by cases result <;> rfl
  simp only [checkSource, positive, ↓reduceDIte, Option.map_some, mapped, Option.some.injEq]
  exact (FiniteMuCalculus.check_positive_iff (model table) formula positive environment budget
    (observation.states source) enough).trans
      (satisfies_pullback observation formula coverage positive environment.meaning source)

omit [Fintype State] [DecidableEq State] in
/-- A Büchi query needs outgoing coverage only, regardless of incoming edges. -/
theorem buchi_coverage {original : ReductionSpan.{v, f} Source}
    (observation : SpanMap original span) (outgoing : observation.SourceLifts) :
    CoversFormula observation (Formula.buchi .future) := by
  exact ⟨⟨trivial, outgoing, trivial⟩, outgoing, trivial⟩

theorem check_buchi_iff (table : FiniteGraph.Table span) (accepting : Finset State)
    (budget : Nat) (state : State)
    (enough : FiniteMuCalculus.requiredBudget (State := State) (Formula.buchi Traversal.future) ≤ budget) :
    ((check table (Formula.buchi .future) (fun _ => accepting) budget state).map Outcome.answer) =
        some (some true) ↔
      BuchiPath (transitionSystem span) .future (↑accepting : Set State) state :=
  (check_positive_iff table _ (Formula.buchi_positive _) _ budget state enough).trans
    (satisfies_buchi_iff_path (transitionSystem span) .future ↑accepting state)

end Mettapedia.OSLF.NativeTypes.Executable.Finite
