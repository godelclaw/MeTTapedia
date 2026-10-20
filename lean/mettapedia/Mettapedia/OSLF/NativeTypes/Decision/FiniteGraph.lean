import Mettapedia.OSLF.NativeTypes.Decision.FiniteFixedPoints
import Mettapedia.OSLF.NativeTypes.Semantics.ObservedFixedPoints

/-!
# Finite transition tables for native fixed-point strategies

The table covers every edge of the specified span in both directions. This
is a certificate for a complete finite model, not a consequence of settling
a forward search from one root. In particular the incoming strategy needs
the table's full predecessor coverage. Event identities stay in the span;
the Boolean table is used only for these predicate observations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Decision.FiniteGraph

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.NativeTypes.Semantics.ObservedFixedPoints
open FiniteFixedPoints

universe u v e f
variable {State : Type u}

structure Table (span : ReductionSpan.{u, e} State) where
  edge : State → State → Bool
  exact : ∀ source target, edge source target = true ↔
    ∃ event : span.Edge, span.source event = source ∧ span.target event = target

namespace Table

variable {span : ReductionSpan.{u, e} State} (table : Table span)
variable [Fintype State] [DecidableEq State]

def reachStep (goal candidate : Finset State) : Finset State :=
  Finset.univ.filter fun source => source ∈ goal ∨ ∃ target ∈ candidate,
    table.edge source target = true

def pastStep (safe candidate : Finset State) : Finset State :=
  Finset.univ.filter fun target => target ∈ safe ∧ ∀ source,
    table.edge source target = true → source ∈ candidate

theorem reachStep_correct (goal candidate : Finset State) :
    (↑(table.reachStep goal candidate) : Set State) = reachOperator span ↑goal ↑candidate := by
  ext source
  simp only [reachStep, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
  change (_ ∨ _) ↔ (_ ∨ derivedDiamond span (↑candidate : Set State) source)
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨target, member, edge⟩
    obtain ⟨event, starts, ends⟩ := (table.exact _ _).mp edge
    refine ⟨event, starts, ?_⟩
    change span.target event ∈ candidate
    rw [ends]
    exact member
  · rintro ⟨event, starts, member⟩
    exact ⟨span.target event, member, (table.exact _ _).mpr ⟨event, starts, rfl⟩⟩

theorem pastStep_correct (safe candidate : Finset State) :
    (↑(table.pastStep safe candidate) : Set State) = pastOperator span ↑safe ↑candidate := by
  ext target
  simp only [pastStep, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
  change (_ ∧ _) ↔ (_ ∧ derivedBox span (↑candidate : Set State) target)
  apply and_congr Iff.rfl
  constructor
  · intro holds event ends
    exact holds _ ((table.exact _ _).mpr ⟨event, rfl, ends⟩)
  · intro holds source edge
    obtain ⟨event, starts, ends⟩ := (table.exact _ _).mp edge
    have member := holds event ends
    change span.source event ∈ candidate at member
    rw [starts] at member
    exact member

def reachStrategy (goal : Finset State) : Strategy (reachOperator span ↑goal) where
  step := table.reachStep goal
  step_correct := table.reachStep_correct goal

def pastStrategy (safe : Finset State) : Strategy (pastOperator span ↑safe) where
  step := table.pastStep safe
  step_correct := table.pastStep_correct safe

/-- A finite answer is about the source span only after outgoing coverage
has been proved for its observation into this table. -/
theorem reach_answer_source {Source : Type v} {original : ReductionSpan.{v, f} Source}
    (observation : Mettapedia.GSLT.ObservationSpans.SpanMap original span)
    (coverage : observation.SourceLifts) (goal : Finset State) (budget : Nat)
    (enough : Fintype.card State ≤ budget) (source : Source) :
    ((table.reachStrategy goal).least budget (observation.states source)).answer = some true ↔
      source ∈ (reachOperator original (observation.states ⁻¹' (↑goal : Set State))).lfp := by
  refine ((table.reachStrategy goal).least_positive_iff budget _ enough).trans ?_
  exact Set.ext_iff.mp (reach_lfp observation coverage (↑goal : Set State)) source

theorem past_answer_source {Source : Type v} {original : ReductionSpan.{v, f} Source}
    (observation : Mettapedia.GSLT.ObservationSpans.SpanMap original span)
    (coverage : observation.TargetLifts) (safe : Finset State) (budget : Nat)
    (enough : Fintype.card State ≤ budget) (source : Source) :
    ((table.pastStrategy safe).greatest budget (observation.states source)).answer = some true ↔
      source ∈ (pastOperator original (observation.states ⁻¹' (↑safe : Set State))).gfp := by
  refine ((table.pastStrategy safe).greatest_positive_iff budget _ enough).trans ?_
  exact Set.ext_iff.mp (past_gfp observation coverage (↑safe : Set State)) source

end Table

section Material

open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.ObservedMaterialization
open Mettapedia.OSLF.Bridges.TypeTheory.ObservedNativeTypes
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

variable {S : GSLT.{u}} {M : System.{u, u} S}
variable (readings : LabelReadings M) (occurrences : ActionOccurrences M)
variable [Fintype (MaterialState readings)] [DecidableEq (MaterialState readings)]

/-- The finite material computation reflects full source reachability. The
finite enumeration and edge table are explicit implementation obligations. -/
theorem material_reach_answer
    (table : Table (ObservedFamilyEnclosure.Events.memberSpan readings occurrences))
    (faithful : readings.Faithful) (complete : ActionsPresentSteps (M := M))
    (goal : Finset (MaterialState readings)) (budget : Nat)
    (enough : Fintype.card (MaterialState readings) ≤ budget) (source : S.Term) :
    ((table.reachStrategy goal).least budget
      (ObservedFamilyEnclosure.valueMember readings source)).answer = some true ↔
    source ∈ (reachOperator (gsltSpan S)
      (ObservedFamilyEnclosure.valueMember readings ⁻¹' (↑goal : Set (MaterialState readings)))).lfp := by
  refine ((table.reachStrategy goal).least_positive_iff budget _ enough).trans ?_
  exact Set.ext_iff.mp (material_reach_lfp readings occurrences faithful complete
    (↑goal : Set (MaterialState readings))) source

theorem material_past_answer
    (table : Table (ObservedFamilyEnclosure.Events.memberSpan readings occurrences))
    (complete : ActionsPresentSteps (M := M))
    (incoming : (ObservedFamilyEnclosure.Events.observation readings occurrences).TargetLifts)
    (safe : Finset (MaterialState readings)) (budget : Nat)
    (enough : Fintype.card (MaterialState readings) ≤ budget) (source : S.Term) :
    ((table.pastStrategy safe).greatest budget
      (ObservedFamilyEnclosure.valueMember readings source)).answer = some true ↔
    source ∈ (pastOperator (gsltSpan S)
      (ObservedFamilyEnclosure.valueMember readings ⁻¹' (↑safe : Set (MaterialState readings)))).gfp := by
  refine ((table.pastStrategy safe).greatest_positive_iff budget _ enough).trans ?_
  exact Set.ext_iff.mp (material_past_gfp readings occurrences complete incoming
    (↑safe : Set (MaterialState readings))) source

end Material

end Mettapedia.OSLF.NativeTypes.Decision.FiniteGraph
