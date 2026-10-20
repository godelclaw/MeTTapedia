import Mettapedia.OSLF.NativeTypes.Decision.FiniteGraph

/-!
# Cyclic reachability and incoming invariants on a finite authored graph

The source relation has three event constructors. Its finite table is checked
against that relation. State zero can loop or finish; state two can enter it;
state three is isolated. A least-fixed-point witness does not make the
underlying process well-founded.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.FiniteGraph.Controls

open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Semantics.ObservedFixedPoints

abbrev State := Fin 4

inductive Step : State → State → Prop where
  | loop : Step 0 0
  | finish : Step 0 1
  | enter : Step 2 0

def theory := equalityGSLT State Step

def span : Mettapedia.OSLF.Framework.DerivedModalities.ReductionSpan State := gsltSpan theory

def edge (source target : State) : Bool :=
  decide ((source = 0 ∧ target = 0) ∨ (source = 0 ∧ target = 1) ∨
    (source = 2 ∧ target = 0))

theorem edge_exact (source target : State) : edge source target = true ↔ Step source target := by
  simp only [edge, decide_eq_true_eq]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact .loop
    · exact .finish
    · exact .enter
  · intro step
    cases step <;> decide

def table : Table span where
  edge := edge
  exact source target := (edge_exact source target).trans
    (gsltSpan_edge_iff_step theory source target).symm

/-- A forward table rooted at zero can omit the predecessor two. Such a
table cannot satisfy the global edge-coverage contract. -/
theorem missing_predecessor_rejects_table :
    ¬ ∃ incomplete : Table span, incomplete.edge 2 0 = false := by
  rintro ⟨incomplete, omitted⟩
  have actual : Step 2 0 := .enter
  have represented := (gsltSpan_edge_iff_step theory (2 : State) (0 : State)).mpr actual
  have present := (incomplete.exact 2 0).mpr represented
  rw [omitted] at present
  cases present

def reach := table.reachStrategy {1}
def past := table.pastStrategy {0, 1, 3}

theorem reach_zero_budget : (reach.least 0 0).answer = none := by decide +kernel
theorem goal_is_reachable_from_loop : (reach.least 2 0).answer = some true := by decide +kernel
theorem entering_process_reaches_goal : (reach.least 3 2).answer = some true := by decide +kernel
theorem isolated_refuted_at_bound : (reach.least 4 3).answer = some false := by decide +kernel

theorem looping_process_satisfies_mu : (0 : State) ∈ (reachOperator span {1}).lfp := by
  simpa only [Finset.coe_singleton] using
    Reference.Core.Outcome.positive (reach.least 2 0) goal_is_reachable_from_loop

theorem looping_process_not_accessible : ¬ Acc Step (0 : State) := by
  have noLoop : ∀ state, Acc Step state → ¬ Step state state := by
    intro state accessible
    induction accessible with
    | intro state _ ih =>
      intro selfStep
      exact ih state selfStep selfStep
  exact fun accessible => noLoop 0 accessible .loop

theorem looping_process_not_outgoing_wellFounded : ¬ Acc (flip Step) (0 : State) := by
  have noLoop : ∀ state, Acc (flip Step) state → ¬ Step state state := by
    intro state accessible
    induction accessible with
    | intro state _ ih =>
      intro selfStep
      exact ih state selfStep selfStep
  exact fun accessible => noLoop 0 accessible .loop

/-- The finite incoming invariant detects the excluded predecessor two,
although two cannot be reached by forward exploration rooted at zero. -/
theorem bad_past_not_yet_seen : (past.greatest 1 1).answer = none := by decide +kernel
theorem bad_past_propagates : (past.greatest 3 1).answer = some false := by decide +kernel
theorem isolated_past_holds : (past.greatest 4 3).answer = some true := by decide +kernel
theorem incoming_is_not_outgoing : table.pastStep Finset.univ ∅ = {2, 3} := by decide +kernel
theorem resumed_reach :
    ((((reach.begin ∅).resume 1).resume 2).least 2).answer = some true := by decide +kernel

/-- The general transport theorem applies to this actual complete table;
the scope is the four-state authored source, not an inferred larger graph. -/
theorem source_reach_exact (source : State) :
    (reach.least 4 source).answer = some true ↔
      source ∈ (reachOperator span {1}).lfp := by
  simpa [reach, Mettapedia.GSLT.ObservationSpans.SpanMap.identity] using
    table.reach_answer_source
      (Mettapedia.GSLT.ObservationSpans.SpanMap.identity span)
      (Mettapedia.GSLT.ObservationSpans.SpanMap.identity_sourceLifts span)
      {1} 4 (by decide) source

def run : IO Unit := do
  let checks := [
    (reach.least 0 0).answer == none,
    (reach.least 2 0).answer == some true,
    (reach.least 3 2).answer == some true,
    (reach.least 4 3).answer == some false,
    (past.greatest 1 1).answer == none,
    (past.greatest 3 1).answer == some false,
    (past.greatest 4 3).answer == some true,
    table.pastStep Finset.univ ∅ == {2, 3},
    ((((reach.begin ∅).resume 1).resume 2).least 2).answer == some true]
  if !checks.all id then throw (IO.userError "Finite native graph control failed")
  IO.println s!"Finite native graph controls: {checks.length} passed"

#eval run

end Mettapedia.OSLF.NativeTypes.Decision.FiniteGraph.Controls
