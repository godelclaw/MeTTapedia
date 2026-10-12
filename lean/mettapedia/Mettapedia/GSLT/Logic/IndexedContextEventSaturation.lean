import Mettapedia.GSLT.Logic.HigherOrderBisimulation
import Mathlib.CategoryTheory.Types.Basic

/-!
# Saturated event observations over an actual context action

A functor supplies the complete action of contexts on interface-indexed
states. Independently supplied events retain their two endpoints. Saturation
tests a state after every context, both for event occurrence and for the
declared observations. Its greatest bisimulation is a contextual congruence
without a relative-pushout assumption.

The event carrier is not quotiented by equality of endpoints. These results
do not claim existence of minimal labels or compare behavioral payloads.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedContextEventSaturation

open CategoryTheory HigherOrderBisimulation

universe u v w e a

variable {C : Type u} [Category.{v} C] (states : C ⥤ Type w)

structure Data (Event : C → Type e) (Atom : C → Type a) where
  source : {interface : C} → Event interface → states.obj interface
  target : {interface : C} → Event interface → states.obj interface
  observes : {interface : C} → Atom interface → states.obj interface → Prop

namespace Data

variable {states} {Event : C → Type e} {Atom : C → Type a}
  (data : Data states Event Atom)

/-- An actual event occurrence supplies both endpoints. -/
def Step {interface : C} (before after : states.obj interface) : Prop :=
  ∃ event : Event interface, data.source event = before ∧ data.target event = after

/-- A firing keeps the supplied event, context and exact endpoint squares. -/
structure Firing {sourceInterface targetInterface : C}
    (context : sourceInterface ⟶ targetInterface)
    (before : states.obj sourceInterface) (after : states.obj targetInterface) where
  event : Event targetInterface
  source_eq : data.source event = states.map context before
  target_eq : data.target event = after

theorem firing_iff_step {sourceInterface targetInterface : C}
    (context : sourceInterface ⟶ targetInterface)
    (before : states.obj sourceInterface) (after : states.obj targetInterface) :
    Nonempty (data.Firing context before after) ↔
      data.Step (states.map context before) after := by
  constructor
  · rintro ⟨firing⟩
    exact ⟨firing.event, firing.source_eq, firing.target_eq⟩
  · rintro ⟨event, sourceEq, targetEq⟩
    exact ⟨⟨event, sourceEq, targetEq⟩⟩

/-- An observation may be made at any future interface after an actual context. -/
abbrev ContextAtom (interface : C) :=
  (future : C) × (interface ⟶ future) × Atom future

def system :
    System (literalVocabulary (fun source target : C => source ⟶ target)) states.obj where
  act label before after := data.Step (states.map label.skeleton before) after
  Atom := ContextAtom (Atom := Atom)
  observes atom value := data.observes atom.2.2 (states.map atom.2.1 value)

abbrev Bisimilar := data.system.Bisimilar

theorem forward {interface future : C} {left right : states.obj interface}
    (related : data.Bisimilar interface left right) (context : interface ⟶ future)
    {next : states.obj future} (step : data.Step (states.map context left) next) :
    ∃ matched, data.Step (states.map context right) matched ∧
      data.Bisimilar future next matched := by
  obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ :=
    (data.system.bisimilar_unfold.mp related).1 (literalLabel context) next step
  have same : context = matchedLabel.skeleton :=
    (relates_literal_iff data.Bisimilar (literalLabel context) matchedLabel).mp labels
  change data.Step (states.map matchedLabel.skeleton right) matched at matchedStep
  rw [← same] at matchedStep
  exact ⟨matched, matchedStep, successors⟩

theorem backward {interface future : C} {left right : states.obj interface}
    (related : data.Bisimilar interface left right) (context : interface ⟶ future)
    {next : states.obj future} (step : data.Step (states.map context right) next) :
    ∃ matched, data.Step (states.map context left) matched ∧
      data.Bisimilar future matched next := by
  obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ :=
    (data.system.bisimilar_unfold.mp related).2.1 (literalLabel context) next step
  have same : matchedLabel.skeleton = context :=
    (relates_literal_iff data.Bisimilar matchedLabel (literalLabel context)).mp labels
  change data.Step (states.map matchedLabel.skeleton left) matched at matchedStep
  rw [same] at matchedStep
  exact ⟨matched, matchedStep, successors⟩

theorem complete_observation {interface future : C} {left right : states.obj interface}
    (related : data.Bisimilar interface left right) (context : interface ⟶ future)
    (atom : Atom future) :
    data.observes atom (states.map context left) ↔
      data.observes atom (states.map context right) :=
  data.system.observes_iff related ⟨future, context, atom⟩

/-- Context closure is formed from related inner states; it is not an
assumed congruence of the behavior being constructed. -/
def ContextClosure (interface : C) (left right : states.obj interface) : Prop :=
  ∃ innerInterface, ∃ innerLeft innerRight : states.obj innerInterface,
    ∃ context : innerInterface ⟶ interface,
      data.Bisimilar innerInterface innerLeft innerRight ∧
        states.map context innerLeft = left ∧ states.map context innerRight = right

theorem into_contextClosure {interface : C} {left right : states.obj interface}
    (related : data.Bisimilar interface left right) :
    data.ContextClosure interface left right := by
  refine ⟨interface, left, right, 𝟙 interface, related, ?_, ?_⟩ <;>
    simp only [Functor.map_id_apply]

theorem contextClosure_progress :
    data.ContextClosure ≤ data.system.progress data.ContextClosure := by
  rintro interface left right ⟨innerInterface, innerLeft, innerRight, context, related, rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro future label next step
    change data.Step (states.map label.skeleton (states.map context innerLeft)) next at step
    have innerStep : data.Step (states.map (context ≫ label.skeleton) innerLeft) next := by
      exact (congrArg (fun value => data.Step value next)
        (states.map_comp_apply context label.skeleton innerLeft)).mpr step
    obtain ⟨matched, matchedStep, successors⟩ := data.forward related _ innerStep
    refine ⟨literalLabel label.skeleton, matched, ?_,
      (relates_literal_iff data.ContextClosure label (literalLabel label.skeleton)).mpr rfl,
      data.into_contextClosure successors⟩
    change data.Step (states.map label.skeleton (states.map context innerRight)) matched
    exact (congrArg (fun value => data.Step value matched)
      (states.map_comp_apply context label.skeleton innerRight)).mp matchedStep
  · intro future label next step
    change data.Step (states.map label.skeleton (states.map context innerRight)) next at step
    have innerStep : data.Step (states.map (context ≫ label.skeleton) innerRight) next := by
      exact (congrArg (fun value => data.Step value next)
        (states.map_comp_apply context label.skeleton innerRight)).mpr step
    obtain ⟨matched, matchedStep, successors⟩ := data.backward related _ innerStep
    refine ⟨literalLabel label.skeleton, matched, ?_,
      (relates_literal_iff data.ContextClosure (literalLabel label.skeleton) label).mpr rfl,
      data.into_contextClosure successors⟩
    change data.Step (states.map label.skeleton (states.map context innerLeft)) matched
    exact (congrArg (fun value => data.Step value matched)
      (states.map_comp_apply context label.skeleton innerLeft)).mp matchedStep
  · rintro ⟨future, outer, atom⟩
    change data.observes atom (states.map outer (states.map context innerLeft)) ↔
      data.observes atom (states.map outer (states.map context innerRight))
    simpa only [Functor.map_comp_apply] using
      data.complete_observation related (context ≫ outer) atom

/-- Saturated bisimilarity respects every actual context action. -/
theorem context_congruent {interface future : C} {left right : states.obj interface}
    (related : data.Bisimilar interface left right) (context : interface ⟶ future) :
    data.Bisimilar future (states.map context left) (states.map context right) :=
  data.system.coinduction data.contextClosure_progress future _ _
    ⟨interface, left, right, context, related, rfl, rfl⟩

/-- Ordinary event bisimulation and direct observations, before saturation. -/
def ReductionBisimulation (relation : RelationFamily states.obj) : Prop :=
  ∀ interface left right, relation interface left right →
    (∀ next, data.Step left next → ∃ matched, data.Step right matched ∧ relation interface next matched) ∧
    (∀ next, data.Step right next → ∃ matched, data.Step left matched ∧ relation interface matched next) ∧
    (∀ atom, data.observes atom left ↔ data.observes atom right)

def ContextClosed (relation : RelationFamily states.obj) : Prop :=
  ∀ {interface future : C} {left right : states.obj interface},
    relation interface left right → (context : interface ⟶ future) →
      relation future (states.map context left) (states.map context right)

theorem bisimilar_reduction : data.ReductionBisimulation data.Bisimilar := by
  intro interface left right related
  refine ⟨?_, ?_, ?_⟩
  · intro next step
    have atIdentity : data.Step (states.map (𝟙 interface) left) next := by
      simpa only [Functor.map_id_apply] using step
    obtain ⟨matched, matchedStep, successors⟩ := data.forward related (𝟙 interface) atIdentity
    exact ⟨matched, by simpa only [Functor.map_id_apply] using matchedStep, successors⟩
  · intro next step
    have atIdentity : data.Step (states.map (𝟙 interface) right) next := by
      simpa only [Functor.map_id_apply] using step
    obtain ⟨matched, matchedStep, successors⟩ := data.backward related (𝟙 interface) atIdentity
    exact ⟨matched, by simpa only [Functor.map_id_apply] using matchedStep, successors⟩
  · intro atom
    simpa only [Functor.map_id_apply] using
      data.complete_observation related (𝟙 interface) atom

/-- Every context-closed event bisimulation is contained in the independently
constructed greatest saturated bisimulation. -/
theorem largest {relation : RelationFamily states.obj}
    (reduction : data.ReductionBisimulation relation) (contexts : ContextClosed relation) :
    relation ≤ data.Bisimilar := by
  apply data.system.coinduction
  intro interface left right related
  refine ⟨?_, ?_, ?_⟩
  · intro future label next step
    obtain ⟨matched, matchedStep, successors⟩ :=
      (reduction future _ _ (contexts related label.skeleton)).1 next step
    exact ⟨literalLabel label.skeleton, matched, matchedStep,
      (relates_literal_iff relation label (literalLabel label.skeleton)).mpr rfl, successors⟩
  · intro future label next step
    obtain ⟨matched, matchedStep, successors⟩ :=
      (reduction future _ _ (contexts related label.skeleton)).2.1 next step
    exact ⟨literalLabel label.skeleton, matched, matchedStep,
      (relates_literal_iff relation (literalLabel label.skeleton) label).mpr rfl, successors⟩
  · rintro ⟨future, context, atom⟩
    exact (reduction future _ _ (contexts related context)).2.2 atom

/-- Saturation earns exactly the largest context-closed reduction
bisimulation, with the declared observations. -/
theorem bisimilar_iff_contextual {interface : C} (left right : states.obj interface) :
    data.Bisimilar interface left right ↔
      ∃ relation, data.ReductionBisimulation relation ∧ ContextClosed relation ∧
        relation interface left right := by
  constructor
  · intro related
    exact ⟨data.Bisimilar, data.bisimilar_reduction,
      fun {_ _ _ _} => data.context_congruent, related⟩
  · rintro ⟨relation, reduction, contexts, related⟩
    exact data.largest reduction contexts interface left right related

end Data

end Mettapedia.GSLT.IndexedContextEventSaturation
