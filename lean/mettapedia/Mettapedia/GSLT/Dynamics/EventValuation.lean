import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.Dynamics.QueryRevision
import Mettapedia.GSLT.Dynamics.IndexedEventValuation
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Nat

/-!
# Indexed valuations of revision events

Evidence, execution work, latency, energy, and authority can all decorate the
same semantic event graph, but they need not share one total algebra.  This
module attaches the existing GSLT `PartialMonoid` to query/revision events.

The separation is intentional:

* a commuting square is behavioral permission;
* a successful partial merge is resource permission;
* parallelizability requires both.

The partial operation accommodates linear or unavailable capabilities, while
ordinary additive quantities use the total additive instance below.

A successful merge alone does not license reversing its order. Actual-path
interchange and equality of the two local compositions retain the final world
and selected grade through a complete continuation. Chronological observations
retain their own order; worker preparation may overlap while publication keeps
the original order.
-/

namespace Mettapedia.GSLT.Dynamics.EventValuation

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.QueryRevision

universe uGrade uLeft uRight

/-- Revision-event instance of the shared event valuation interface. -/
abbrev Valuation (theory : Theory) :=
  IndexedEventValuation.Valuation.{_, uGrade} theory.Revision

namespace Valuation

/-- Combine two independently chosen event valuations.  The resulting grade
retains both components, and a merge succeeds only when both partial algebras
accept it. -/
abbrev prod {theory : Theory}
    (left : Valuation.{uLeft} theory) (right : Valuation.{uRight} theory) :
    Valuation theory :=
  IndexedEventValuation.Valuation.prod left right

/-- Fold a chronological event history through its declared partial algebra. -/
abbrev historyGrade {theory : Theory} (valuation : Valuation theory) :
    List theory.Revision → Option valuation.Grade :=
  IndexedEventValuation.Valuation.historyGrade valuation

@[simp] theorem historyGrade_nil {theory : Theory}
    (valuation : Valuation theory) :
    valuation.historyGrade [] = some valuation.algebra.unit :=
  rfl

@[simp] theorem historyGrade_cons {theory : Theory}
    (valuation : Valuation theory) (revision : theory.Revision)
    (revisions : List theory.Revision) :
    valuation.historyGrade (revision :: revisions) =
      (valuation.grade revision).bind fun head =>
        (valuation.historyGrade revisions).bind fun tail =>
          valuation.algebra.op head tail :=
  rfl

/-- History valuation is compositional under chronological concatenation. -/
theorem historyGrade_append {theory : Theory}
    (valuation : Valuation theory)
    (first second : List theory.Revision) :
    valuation.historyGrade (first ++ second) =
      (valuation.historyGrade first).bind fun left =>
        (valuation.historyGrade second).bind fun right =>
          valuation.algebra.op left right :=
  IndexedEventValuation.Valuation.historyGrade_append valuation first second

/-- Attempt to combine the grades of two candidate concurrent events. -/
abbrev combine? {theory : Theory} (valuation : Valuation theory)
    (first second : theory.Revision) : Option valuation.Grade :=
  IndexedEventValuation.Valuation.combine? valuation first second

/-- Resource compatibility is successful composition in the selected
valuation algebra. -/
abbrev Compatible {theory : Theory} (valuation : Valuation theory)
    (first second : theory.Revision) : Prop :=
  IndexedEventValuation.Valuation.Compatible valuation first second

/-- Strong parallelizability requires a literal semantic square and resource
compatibility. -/
def StronglyParallelizable {theory : Theory} (valuation : Valuation theory)
    (first second : theory.Revision) (source : theory.World) : Prop :=
  theory.StronglyCoexecutible first second source ∧
    valuation.Compatible first second

/-- Observer-relative parallelizability permits distinct internal residuals
when the complete declared query profile agrees. -/
def QueryParallelizable {theory : Theory} (valuation : Valuation theory)
    (first second : theory.Revision) (source : theory.World) : Prop :=
  theory.QueryCoexecutible first second source ∧
    valuation.Compatible first second

/-- Every strong parallelization certificate is also valid at the complete
query profile. -/
theorem stronglyParallelizable_implies_queryParallelizable
    {theory : Theory} {valuation : Valuation theory}
    {first second : theory.Revision} {source : theory.World}
    (parallelizable :
      valuation.StronglyParallelizable first second source) :
    valuation.QueryParallelizable first second source :=
  ⟨theory.stronglyCoexecutible_implies_queryCoexecutible parallelizable.1,
    parallelizable.2⟩

/-- Componentwise compatibility grants compatibility of the product
valuation. -/
theorem prod_compatible {theory : Theory}
    (left : Valuation.{uLeft} theory) (right : Valuation.{uRight} theory)
    (first second : theory.Revision)
    (leftCompatible : left.Compatible first second)
    (rightCompatible : right.Compatible first second) :
    (left.prod right).Compatible first second :=
  IndexedEventValuation.Valuation.prod_compatible left right first second
    leftCompatible rightCompatible

/-- Actual-path interchange and the declared local algebra law preserve the
full final world and that valuation through the same complete continuation.
No chronological or derivation-bag equality is inferred. -/
theorem swap_actual_history {theory : Theory} (valuation : Valuation theory)
    {first second : theory.Revision}
    (interchange : ∀ {source middle target : theory.World},
      theory.Step first source middle → theory.Step second middle target →
        ∃ afterSecond, theory.Step second source afterSecond ∧
          theory.Step first afterSecond target)
    (orderAgrees : valuation.combine? first second = valuation.combine? second first)
    (preceding following : List theory.Revision) {source target : theory.World}
    (steps : theory.HistoryStep (preceding ++ first :: second :: following) source target) :
    theory.HistoryStep (preceding ++ second :: first :: following) source target ∧
      valuation.historyGrade (preceding ++ first :: second :: following) =
        valuation.historyGrade (preceding ++ second :: first :: following) :=
  ⟨Theory.HistoryStep.swap_adjacent interchange preceding following steps,
    IndexedEventValuation.Valuation.historyGrade_swap_adjacent valuation orderAgrees
      preceding following⟩


/-- Whole finite trace transport retains the actual final world, the
declared partial grade and all revision occurrences. Only swaps licensed by
both state interchange and local grade agreement are identified. -/
theorem trace_preserves_actual_world_and_grade {theory : Theory}
    (valuation : Valuation theory)
    (independent : theory.Revision → theory.Revision → Prop)
    (symmetric : ∀ {first second}, independent first second → independent second first)
    (interchange : ∀ {first second : theory.Revision}
      {source middle target : theory.World}, independent first second →
      theory.Step first source middle → theory.Step second middle target →
        ∃ afterSecond, theory.Step second source afterSecond ∧
          theory.Step first afterSecond target)
    (lawful : ∀ first second, independent first second →
      valuation.combine? first second = valuation.combine? second first)
    {first second : List theory.Revision}
    (equivalent : Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv
      independent first second) {source target : theory.World}
    (steps : theory.HistoryStep first source target) :
    theory.HistoryStep second source target ∧
      valuation.historyGrade first = valuation.historyGrade second ∧
      first.Perm second :=
  ⟨(Theory.HistoryStep.traceEquiv_iff independent symmetric interchange
      equivalent source target).mp steps,
    IndexedEventValuation.Valuation.historyGrade_traceEquiv
      valuation independent lawful equivalent,
    Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv.perm equivalent⟩

end Valuation

/-! ## Total additive valuations -/

/-- Any additive monoid is a total instance of the partial composition
interface. -/
abbrev additivePartialMonoid (Grade : Type uGrade) [AddMonoid Grade] :
    PartialMonoid Grade := IndexedEventValuation.additivePartialMonoid Grade

/-- Attach an ordinary additive grade to every event. -/
abbrev additive {theory : Theory} {Grade : Type uGrade} [AddMonoid Grade]
    (grade : theory.Revision → Grade) : Valuation theory :=
  IndexedEventValuation.additive grade

@[simp] theorem additive_combine {theory : Theory}
    {Grade : Type uGrade} [AddMonoid Grade]
    (grade : theory.Revision → Grade) (first second : theory.Revision) :
    (additive grade).combine? first second =
      some (grade first + grade second) :=
  rfl

theorem additive_compatible {theory : Theory}
    {Grade : Type uGrade} [AddMonoid Grade]
    (grade : theory.Revision → Grade) (first second : theory.Revision) :
    (additive grade).Compatible first second := by
  change (some (grade first + grade second)).isSome = true
  rfl

/-- Count revision events without assigning any backend-specific duration or
memory model. -/
def eventCount (theory : Theory) : Valuation theory :=
  additive (Grade := Nat) fun _ => 1

/-! ## Certified backend-specific parallel admission -/

/-- A backend may conservatively select a subset of query-preserving,
resource-compatible event pairs for parallel execution.  Backends share the
same semantic theory; they may differ in valuation and admitted plan set. -/
structure ParallelBackend (theory : Theory) where
  valuation : Valuation.{uGrade} theory
  Admits : theory.Revision → theory.Revision → theory.World → Prop
  sound : ∀ {first second source}, Admits first second source →
    valuation.QueryParallelizable first second source

namespace ParallelBackend

/-- Backend admission is always sound for the declared query profile. -/
theorem admitted_queryCoexecutible {theory : Theory}
    (backend : ParallelBackend.{uGrade} theory)
    {first second : theory.Revision} {source : theory.World}
    (admitted : backend.Admits first second source) :
    theory.QueryCoexecutible first second source :=
  (backend.sound admitted).1

/-- One backend has at least the parallel-plan inventory of another when it
admits every pair admitted by the other. -/
def Subsumes {theory : Theory}
    (more less : ParallelBackend.{uGrade} theory) : Prop :=
  ∀ {first second source}, less.Admits first second source →
    more.Admits first second source

end ParallelBackend

namespace Controls

/-- The nondeterministic coordinate instance preserves all actual endpoints
and additive work through arbitrary generated finite trace rearrangements. -/
theorem independent_finite_trace_preserves_world_and_work (cost : Bool → Nat)
    {first second : List Bool}
    (equivalent : Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv
      (· ≠ ·) first second) {source target : Nat × Nat}
    (steps : QueryRevision.Controls.independentBranchingTheory.HistoryStep
      first source target) :
    QueryRevision.Controls.independentBranchingTheory.HistoryStep second source target ∧
      (additive (theory := QueryRevision.Controls.independentBranchingTheory) cost).historyGrade
        first =
      (additive (theory := QueryRevision.Controls.independentBranchingTheory) cost).historyGrade
        second ∧ first.Perm second :=
  Valuation.trace_preserves_actual_world_and_grade
    (additive (theory := QueryRevision.Controls.independentBranchingTheory) cost)
    (· ≠ ·) Ne.symm QueryRevision.Controls.independent_branching_interchange
    (fun first second _ =>
      IndexedEventValuation.additive_composition_swap cost first second)
    equivalent steps

/-- Two permitted swaps retain a four-event actual run and arbitrary
additive costs, including both repetitions, while chronology still differs. -/
theorem repeated_finite_wave_keeps_world_work_and_chronology (cost : Bool → Nat) :
    QueryRevision.Controls.independentBranchingTheory.HistoryStep
      [true, false, true, false] (0, 0) (2, 6) ∧
    QueryRevision.Controls.independentBranchingTheory.HistoryStep
      [false, true, false, true] (0, 0) (2, 6) ∧
    (additive (theory := QueryRevision.Controls.independentBranchingTheory) cost).historyGrade
      [true, false, true, false] =
    (additive (theory := QueryRevision.Controls.independentBranchingTheory) cost).historyGrade
      [false, true, false, true] ∧
    ([true, false, true, false] : List Bool).Perm [false, true, false, true] ∧
    (IndexedEventValuation.chronological (id : Bool → Bool)).historyGrade
      [true, false, true, false] ≠
    (IndexedEventValuation.chronological (id : Bool → Bool)).historyGrade
      [false, true, false, true] := by
  have one : Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv
      (· ≠ ·) [true, false, true, false] [false, true, true, false] :=
    .rel _ _ (Mettapedia.GSLT.Distinction.CausalGluing.Swap.swap []
      [true, false] (by decide))
  have two : Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv
      (· ≠ ·) [false, true, true, false] [false, true, false, true] :=
    .rel _ _ (Mettapedia.GSLT.Distinction.CausalGluing.Swap.swap [false, true]
      [] (by decide))
  have forward : QueryRevision.Controls.independentBranchingTheory.HistoryStep
      [true, false, true, false] (0, 0) (2, 6) := by
    have first : QueryRevision.Controls.independentBranchingTheory.Step true
        ((0, 0) : Nat × Nat) (1, 0) := by
      simp [QueryRevision.Controls.independentBranchingTheory]
    have second : QueryRevision.Controls.independentBranchingTheory.Step false
        ((1, 0) : Nat × Nat) (1, 3) := by
      simp [QueryRevision.Controls.independentBranchingTheory]
    have third : QueryRevision.Controls.independentBranchingTheory.Step true
        ((1, 3) : Nat × Nat) (2, 3) := by
      simp [QueryRevision.Controls.independentBranchingTheory]
    have fourth : QueryRevision.Controls.independentBranchingTheory.Step false
        ((2, 3) : Nat × Nat) (2, 6) := by
      simp [QueryRevision.Controls.independentBranchingTheory]
    exact .cons first (.cons second (.cons third (.single fourth)))
  have preserved := independent_finite_trace_preserves_world_and_work cost
    (.trans _ _ _ one two) forward
  refine ⟨forward, preserved.1, preserved.2.1, preserved.2.2, ?_⟩
  simp only [IndexedEventValuation.chronological_historyGrade, List.map_id]
  decide

/-- Nondeterministic independent updates preserve arbitrary additive work
and the complete suffix after the two actual operations are interchanged. -/
theorem independent_work_history_swap (cost : Bool → Nat)
    (preceding following : List Bool) {source target : Nat × Nat}
    (steps : QueryRevision.Controls.independentBranchingTheory.HistoryStep
      (preceding ++ true :: false :: following) source target) :
    QueryRevision.Controls.independentBranchingTheory.HistoryStep
      (preceding ++ false :: true :: following) source target ∧
      (additive (theory := QueryRevision.Controls.independentBranchingTheory) cost).historyGrade
        (preceding ++ true :: false :: following) =
      (additive (theory := QueryRevision.Controls.independentBranchingTheory) cost).historyGrade
        (preceding ++ false :: true :: following) :=
  Valuation.swap_actual_history
    (additive (theory := QueryRevision.Controls.independentBranchingTheory) cost)
    QueryRevision.Controls.independent_branching_actual_steps_swap
    (IndexedEventValuation.additive_composition_swap cost true false)
    preceding following steps

/-- The same concrete independent updates can swap actual state paths while
the accepted chronological grade remains different. Compatibility alone
cannot license erasure of its order. -/
theorem independent_state_swap_retains_distinct_chronology :
    QueryRevision.Controls.independentBranchingTheory.HistoryStep [true, false]
      (0, 0) (1, 3) ∧
    QueryRevision.Controls.independentBranchingTheory.HistoryStep [false, true]
      (0, 0) (1, 3) ∧
    (IndexedEventValuation.chronological (id : Bool → Bool)).Compatible true false ∧
    (IndexedEventValuation.chronological (id : Bool → Bool)).Compatible false true ∧
    (IndexedEventValuation.chronological (id : Bool → Bool)).combine? true false ≠
      (IndexedEventValuation.chronological (id : Bool → Bool)).combine? false true := by
  have forward : QueryRevision.Controls.independentBranchingTheory.HistoryStep [true, false]
      (0, 0) (1, 3) :=
    Theory.HistoryStep.two_iff.mpr
      ⟨(1, 0), by simp [QueryRevision.Controls.independentBranchingTheory],
        by simp [QueryRevision.Controls.independentBranchingTheory]⟩
  refine ⟨forward, QueryRevision.Controls.independent_branching_history_swap [] [] forward,
    ?_, ?_, IndexedEventValuation.chronological_composition_cannot_swap true false (by decide)⟩
  · rfl
  · rfl


end Controls

/-! ## Separating canary: behavior is not resource authority -/

namespace Canary

/-- Two no-op events commute semantically.  This deliberately tiny theory is
only a separating model for the resource obligation. -/
def noOpTheory : Theory where
  World := Unit
  Revision := Bool
  Query := Unit
  Observation := Unit
  Step := fun _ source target => target = source
  query := fun _ _ => ()

/-- Every pair of no-op events forms a literal semantic square. -/
def noOpSquare (first second : Bool) :
    noOpTheory.StrongSquare first second () where
  afterFirst := ()
  afterSecond := ()
  joined := ()
  firstFromSource := rfl
  secondFromSource := rfl
  secondAfterFirst := rfl
  firstAfterSecond := rfl

/-- `true` means an event claims one exclusive token.  Two claims cannot be
merged even when their state transitions commute. -/
def exclusiveClaimAlgebra : PartialMonoid Bool where
  unit := false
  op := fun first second =>
    if first && second then none else some (first || second)
  unit_op := by intro value; cases value <;> rfl
  op_unit := by intro value; cases value <;> rfl
  op_assoc := by
    intro first second third
    cases first <;> cases second <;> cases third <;> rfl

/-- Both no-op events claim the same exclusive resource class. -/
def exclusiveValuation : Valuation noOpTheory where
  Grade := Bool
  algebra := exclusiveClaimAlgebra
  grade := fun _ => some true

theorem exclusive_events_not_compatible (first second : Bool) :
    ¬ exclusiveValuation.Compatible first second := by
  change ¬ (none : Option Bool).isSome = true
  decide

/-- Behavioral commutation alone does not grant parallel resource authority. -/
theorem semantic_commutation_does_not_imply_resource_compatibility
    (first second : Bool) :
    noOpTheory.StronglyCoexecutible first second () ∧
      ¬ exclusiveValuation.Compatible first second :=
  ⟨⟨noOpSquare first second⟩,
    exclusive_events_not_compatible first second⟩

/-- Ordinary additive work accounting accepts the same commuting events. -/
def workValuation : Valuation noOpTheory :=
  eventCount noOpTheory

theorem work_events_parallelizable (first second : Bool) :
    workValuation.StronglyParallelizable first second () :=
  ⟨⟨noOpSquare first second⟩,
    additive_compatible (theory := noOpTheory) (Grade := Nat)
      (fun _ => 1) first second⟩

@[simp] theorem two_event_work_grade (first second : Bool) :
    workValuation.historyGrade [first, second] = some (2 : Nat) :=
  rfl

/-- A backend that admits every pair in the no-op theory. -/
def allPairsBackend : ParallelBackend noOpTheory where
  valuation := workValuation
  Admits := fun _ _ _ => True
  sound := by
    intro first second source _
    cases source
    exact work_events_parallelizable first second |>
      Valuation.stronglyParallelizable_implies_queryParallelizable

/-- A sound but conservative backend that admits only equal event classes. -/
def sameClassBackend : ParallelBackend noOpTheory where
  valuation := workValuation
  Admits := fun first second _ => first = second
  sound := by
    intro first second source _
    cases source
    exact work_events_parallelizable first second |>
      Valuation.stronglyParallelizable_implies_queryParallelizable

theorem allPairs_subsumes_sameClass :
    allPairsBackend.Subsumes sameClassBackend := by
  intro first second source _
  trivial

/-- A backend may serialize a behaviorally and resource-compatible pair; its
plan inventory is an implementation capability, not the language meaning. -/
theorem conservative_backend_rejects_commuting_pair :
    noOpTheory.QueryCoexecutible true false () ∧
      workValuation.Compatible true false ∧
      allPairsBackend.Admits true false () ∧
      ¬ sameClassBackend.Admits true false () := by
  exact
    ⟨noOpTheory.stronglyCoexecutible_implies_queryCoexecutible
        ⟨noOpSquare true false⟩,
      additive_compatible (theory := noOpTheory) (Grade := Nat)
        (fun _ => 1) true false,
      trivial,
      by simp [sameClassBackend]⟩

end Canary

end Mettapedia.GSLT.Dynamics.EventValuation
