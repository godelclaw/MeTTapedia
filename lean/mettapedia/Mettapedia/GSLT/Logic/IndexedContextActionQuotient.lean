import Mettapedia.GSLT.Logic.IndexedContextEventSaturation
import Mathlib.CategoryTheory.Quotient

/-!
# The semantic context quotient and complete saturated comparison

Two contexts have the same action when their complete maps on the supplied
state family agree. This is a categorical congruence. Its actual quotient
acts faithfully on that family, and every admitted observer factors uniquely
through it. Saturated bisimilarity is identical before and after this change
of context labels. Every event occurrence survives the comparison.

This quotient concerns equality of complete actions, not an independently
authored equation presentation or equality of execution receipts. It does
not supply relative pushouts or reflect raw minimal labels.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedContextActionQuotient

open _root_.CategoryTheory HigherOrderBisimulation
open IndexedContextEventSaturation

universe u v w e a d h

variable {C : Type u} [Category.{v} C] (states : C ⥤ Type w)

abbrev ContextCategory := CategoryTheory.Quotient states.homRel

def projection : C ⥤ ContextCategory states := CategoryTheory.Quotient.functor states.homRel

/-- The complete action descends through its earned categorical congruence. -/
def action : ContextCategory states ⥤ Type w :=
  CategoryTheory.Quotient.lift states.homRel states (fun _ _ _ _ related => related)

theorem action_factorization : projection states ⋙ action states = states :=
  CategoryTheory.Quotient.lift_spec states.homRel states _

theorem action_reading {source target : C} (context : source ⟶ target)
    (value : states.obj source) :
    (action states).map ((projection states).map context) value = states.map context value := rfl

/-- Equality of quotient contexts is exactly equality of every state filling. -/
theorem context_eq_iff {source target : C} (first second : source ⟶ target) :
    (projection states).map first = (projection states).map second ↔
      ∀ value : states.obj source, states.map first value = states.map second value := by
  change (CategoryTheory.Quotient.functor states.homRel).map first =
    (CategoryTheory.Quotient.functor states.homRel).map second ↔ _
  rw [CategoryTheory.Quotient.functor_map_eq_iff]
  change states.map first = states.map second ↔ _
  constructor
  · intro same value
    exact ConcreteCategory.congr_hom same value
  · intro same
    exact ConcreteCategory.hom_ext _ _ same

instance action_faithful : (action states).Faithful where
  map_injective := by
    rintro ⟨source⟩ ⟨target⟩ first second same
    induction first using Quot.inductionOn with
    | _ first =>
      induction second using Quot.inductionOn with
      | _ second =>
        exact (CategoryTheory.Quotient.functor_map_eq_iff states.homRel first second).mpr same

variable {states} {Event : C → Type e} {Atom : C → Type a}
  (data : Data states Event Atom)

def quotientData :
    Data (action states) (fun interface => Event interface.as) (fun interface => Atom interface.as) where
  source := data.source
  target := data.target
  observes := data.observes

/-- Changing labels retains the actual supplied firing occurrence. -/
def projectFiring {source target : C} {context : source ⟶ target}
    {before : states.obj source} {after : states.obj target}
    (firing : data.Firing context before after) :
    (quotientData data).Firing ((projection states).map context) before after where
  event := firing.event
  source_eq := firing.source_eq
  target_eq := firing.target_eq

/-- A quotient firing at a prescribed raw label recovers the same occurrence,
because the complete action, not just an observation, is unchanged. -/
def recoverFiring {source target : C} {context : source ⟶ target}
    {before : states.obj source} {after : states.obj target}
    (firing : (quotientData data).Firing ((projection states).map context) before after) :
    data.Firing context before after where
  event := firing.event
  source_eq := firing.source_eq
  target_eq := firing.target_eq

theorem firing_roundtrip {source target : C} {context : source ⟶ target}
    {before : states.obj source} {after : states.obj target}
    (firing : data.Firing context before after) :
    recoverFiring data (projectFiring data firing) = firing := by
  cases firing
  rfl

theorem quotient_firing_roundtrip {source target : C} {context : source ⟶ target}
    {before : states.obj source} {after : states.obj target}
    (firing : (quotientData data).Firing ((projection states).map context) before after) :
    projectFiring data (recoverFiring data firing) = firing := by
  cases firing
  rfl

theorem raw_bisimilar_of_quotient {interface : C} {left right : states.obj interface}
    (related : (quotientData data).Bisimilar ((projection states).obj interface) left right) :
    data.Bisimilar interface left right := by
  apply data.system.coinduction
    (relation := fun interface left right =>
      (quotientData data).Bisimilar ((projection states).obj interface) left right)
    ?_ interface left right related
  intro interface first second pair
  refine ⟨?_, ?_, ?_⟩
  · intro future label next step
    obtain ⟨matched, matchedStep, successors⟩ :=
      (quotientData data).forward pair ((projection states).map label.skeleton) step
    exact ⟨literalLabel label.skeleton, matched, matchedStep,
      (relates_literal_iff _ label (literalLabel label.skeleton)).mpr rfl, successors⟩
  · intro future label next step
    obtain ⟨matched, matchedStep, successors⟩ :=
      (quotientData data).backward pair ((projection states).map label.skeleton) step
    exact ⟨literalLabel label.skeleton, matched, matchedStep,
      (relates_literal_iff _ (literalLabel label.skeleton) label).mpr rfl, successors⟩
  · rintro ⟨future, context, atom⟩
    exact (quotientData data).complete_observation pair ((projection states).map context) atom

theorem quotient_bisimilar_of_raw {interface : C} {left right : states.obj interface}
    (related : data.Bisimilar interface left right) :
    (quotientData data).Bisimilar ((projection states).obj interface) left right := by
  apply (quotientData data).system.coinduction
    (relation := fun interface left right => data.Bisimilar interface.as left right)
    ?_ ((projection states).obj interface) left right related
  rintro ⟨interface⟩ first second pair
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨future⟩ label next step
    obtain ⟨context, same⟩ :=
      (CategoryTheory.Quotient.full_functor states.homRel).map_surjective label.skeleton
    change (quotientData data).Step ((action states).map label.skeleton first) next at step
    rw [← same] at step
    obtain ⟨matched, matchedStep, successors⟩ := data.forward pair context step
    refine ⟨literalLabel label.skeleton, matched, ?_,
      (relates_literal_iff _ label (literalLabel label.skeleton)).mpr rfl, successors⟩
    change (quotientData data).Step ((action states).map label.skeleton second) matched
    rw [← same]
    exact matchedStep
  · rintro ⟨future⟩ label next step
    obtain ⟨context, same⟩ :=
      (CategoryTheory.Quotient.full_functor states.homRel).map_surjective label.skeleton
    change (quotientData data).Step ((action states).map label.skeleton second) next at step
    rw [← same] at step
    obtain ⟨matched, matchedStep, successors⟩ := data.backward pair context step
    refine ⟨literalLabel label.skeleton, matched, ?_,
      (relates_literal_iff _ (literalLabel label.skeleton) label).mpr rfl, successors⟩
    change (quotientData data).Step ((action states).map label.skeleton first) matched
    rw [← same]
    exact matchedStep
  · rintro ⟨⟨future⟩, outer, atom⟩
    obtain ⟨context, same⟩ :=
      (CategoryTheory.Quotient.full_functor states.homRel).map_surjective outer
    change data.observes atom ((action states).map outer first) ↔
      data.observes atom ((action states).map outer second)
    rw [← same]
    exact data.complete_observation pair context atom

/-- Both independently constructed greatest fixed points agree on complete
saturated behavior, through every quotient label representative. -/
theorem bisimilar_iff {interface : C} (left right : states.obj interface) :
    (quotientData data).Bisimilar ((projection states).obj interface) left right ↔
      data.Bisimilar interface left right :=
  ⟨raw_bisimilar_of_quotient data, quotient_bisimilar_of_raw data⟩

variable (states) {D : Type d} [Category.{h} D]

/-- Observer admission means respecting equality of complete context actions. -/
def ObserverAdmitted (observer : C ⥤ D) : Prop :=
  ∀ {source target : C} (first second : source ⟶ target),
    (∀ value : states.obj source, states.map first value = states.map second value) →
      observer.map first = observer.map second

def observerExtension (observer : C ⥤ D) (admitted : ObserverAdmitted states observer) :
    ContextCategory states ⥤ D :=
  CategoryTheory.Quotient.lift states.homRel observer (fun _ _ first second related =>
    admitted first second (fun value => ConcreteCategory.congr_hom related value))

theorem observerExtension_factorization (observer : C ⥤ D)
    (admitted : ObserverAdmitted states observer) :
    projection states ⋙ observerExtension states observer admitted = observer :=
  CategoryTheory.Quotient.lift_spec states.homRel observer _

theorem observerExtension_unique (observer : C ⥤ D)
    (admitted : ObserverAdmitted states observer) (candidate : ContextCategory states ⥤ D)
    (square : projection states ⋙ candidate = observer) :
    candidate = observerExtension states observer admitted :=
  CategoryTheory.Quotient.lift_unique states.homRel observer _ candidate square

/-- Complete-action compatibility is necessary and sufficient for a unique
interpretation on the actual semantic context quotient. -/
theorem observerAdmitted_iff_unique_extension (observer : C ⥤ D) :
    ObserverAdmitted states observer ↔
      ∃! candidate : ContextCategory states ⥤ D, projection states ⋙ candidate = observer := by
  constructor
  · intro admitted
    exact ⟨observerExtension states observer admitted,
      observerExtension_factorization states observer admitted,
      fun candidate square => observerExtension_unique states observer admitted candidate square⟩
  · rintro ⟨candidate, square, _unique⟩
    subst observer
    intro source target first second related
    change candidate.map ((projection states).map first) =
      candidate.map ((projection states).map second)
    exact congrArg candidate.map ((context_eq_iff states first second).mpr related)

end Mettapedia.GSLT.IndexedContextActionQuotient
