import Mettapedia.TypeTheory.MaterialSets.Hypersets.Hyperset
import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagModel

/-!
# Observation boundaries for behavioural fixed-point transport

Outgoing graph decoration identifies exactly outgoing bisimilarity. It does
not by itself retain predecessor observations or the spatial multiplicity of
a completed answer bag. These controls use the existing modal and spatial
semantics, rather than replacing either with a Boolean surrogate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.ObservedFixedPointControls

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.MeTTaIL.Syntax

namespace Incoming

/-- A predecessor, its terminal target, and an isolated terminal state. -/
inductive State where
  | predecessor
  | reached
  | isolated
  deriving DecidableEq, Repr

def edge (source target : State) : Prop :=
  source = .predecessor ∧ target = .reached

/-- The sole actual event is retained as the edge of the reduction span. -/
def span : ReductionSpan State where
  Edge := Unit
  source _ := .predecessor
  target _ := .reached

theorem span_exact (source target : State) :
    (∃ event : span.Edge, span.source event = source ∧ span.target event = target) ↔
      edge source target := by
  constructor
  · rintro ⟨_, first, second⟩
    exact ⟨first.symm, second.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨(), rfl, rfl⟩

theorem terminals_bisimilar : Bisimilar edge edge State.reached State.isolated := by
  refine ⟨fun first second => first = .reached ∧ second = .isolated, ?_, rfl, rfl⟩
  rintro _ _ ⟨rfl, rfl⟩
  constructor
  · intro _ step
    cases step.1
  · intro _ step
    cases step.1

theorem terminal_decorations_equal :
    HSet.decorate edge State.reached = HSet.decorate edge State.isolated :=
  HSet.decorate_eq_decorate_iff.mpr terminals_bisimilar

theorem reached_has_predecessor : ¬ derivedBox span (fun _ => False) State.reached := by
  intro holds
  exact holds () rfl

theorem isolated_has_no_predecessor : derivedBox span (fun _ => False) State.isolated := by
  intro _ impossible
  cases impossible

/-- The ordinary decoration cannot support this legitimate native predicate. -/
theorem incoming_box_does_not_factor :
    ¬ ∃ predicate : HSet → Prop, ∀ state,
      predicate (HSet.decorate edge state) ↔ derivedBox span (fun _ => False) state := by
  rintro ⟨predicate, exactMeaning⟩
  have accepted := (exactMeaning State.isolated).mpr isolated_has_no_predecessor
  rw [← terminal_decorations_equal] at accepted
  exact reached_has_predecessor ((exactMeaning State.reached).mp accepted)

/-- The actual event witnesses the corresponding forward observation. -/
theorem communication_target_possible :
    derivedDiamond span (fun state => state = State.reached) State.predecessor :=
  ⟨(), rfl, rfl⟩

/-- With its actual incoming event covered, the predecessor predicate is exact. -/
theorem reached_predecessor_exact (predicate : State → Prop) :
    derivedBox span predicate State.reached ↔ predicate State.predecessor := by
  exact ⟨fun holds => holds () rfl, fun holds _ _ => holds⟩

end Incoming

namespace Multiplicity

open Mettapedia.OSLF.NativeTypes.Decision.Spatial

/-- Static answer observations have equal empty transition behaviour. -/
theorem empty_behaviours_equal (value : Pattern) :
    HSet.decorate BagModel.system.Step [value] =
      HSet.decorate BagModel.system.Step [value, value] := by
  apply HSet.decorate_eq_decorate_iff.mpr
  refine ⟨fun _ _ => True, ?_, trivial⟩
  intro first second _
  constructor
  · intro target step
    exact (BagModel.no_step first target step).elim
  · intro target step
    exact (BagModel.no_step second target step).elim

/-- The shared spatial formula still detects the missing answer occurrence. -/
theorem exact_packet_separates (value : Pattern) :
    BagModel.holds (BagModel.packet [value, value]) [value, value] ∧
      ¬ BagModel.holds (BagModel.packet [value, value]) [value] := by
  constructor
  · exact (BagModel.packet_iff _ _).mpr rfl
  · intro accepted
    have cardinalities := congrArg Multiset.card ((BagModel.packet_iff _ _).mp accepted)
    simp at cardinalities

theorem spatial_packet_does_not_factor (value : Pattern) :
    ¬ ∃ predicate : HSet → Prop, ∀ items : List Pattern,
      predicate (HSet.decorate BagModel.system.Step items) ↔
        BagModel.holds (BagModel.packet [value, value]) items := by
  rintro ⟨predicate, exactMeaning⟩
  have accepted := (exactMeaning [value, value]).mpr (exact_packet_separates value).1
  rw [← empty_behaviours_equal value] at accepted
  exact (exact_packet_separates value).2 ((exactMeaning [value]).mp accepted)

end Multiplicity

end Mettapedia.OSLF.NativeTypes.Semantics.ObservedFixedPointControls
