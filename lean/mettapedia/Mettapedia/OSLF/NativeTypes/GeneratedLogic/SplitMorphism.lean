import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BoundedMorphism

/-!
# Split morphisms

A split morphism carries steps and splits forth and back. Along it, a formula built from steps, splits, the
connectives, variables and fixed points (`Formula.splitForward`) holds at an element exactly when it holds at its image
(`SplitMorphism.sat_iff`). Every bounded morphism is one (`BoundedMorphism.toSplit`).

A split morphism asks nothing of the other shapes. A structure whose elements are bags of payloads, with the payloads
outside it, has split morphisms into the reference structure but no bounded morphism: a singleton's member is a
payload, not an element.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Formula NativeStructure

universe u v

namespace Formula

/-- Whether a formula uses only steps, splits, the connectives, variables and fixed points. -/
def splitForward : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot | _, .var _ => true
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right =>
    splitForward left && splitForward right
  | _, .mu inner | _, .nu inner => splitForward inner
  | _, .possibly label formula | _, .necessarily label formula => !label.isContext && splitForward formula
  | _, _ => false

end Formula

/-- **A split morphism**: steps and splits go forward and come back. -/
structure SplitMorphism {Source : Type u} {Target : Type v} (S : NativeStructure Source)
    (T : NativeStructure Target) where
  map : Source → Target
  step : ∀ {source label target}, label.isContext = false → S.step source label target →
    T.step (map source) label (map target)
  stepBack : ∀ {source label target'}, label.isContext = false → T.step (map source) label target' →
    ∃ target, S.step source label target ∧ map target = target'
  split : ∀ {element kind first second}, S.split element kind first second →
    T.split (map element) kind (map first) (map second)
  splitBack : ∀ {element kind first' second'}, T.split (map element) kind first' second' →
    ∃ first second, S.split element kind first second ∧ map first = first' ∧ map second = second'

/-- A bounded morphism is a split morphism. -/
def BoundedMorphism.toSplit {Source : Type u} {Target : Type v} {S : NativeStructure Source}
    {T : NativeStructure Target} (morphism : BoundedMorphism S T) : SplitMorphism S T :=
  ⟨morphism.map, morphism.step, morphism.stepBack, morphism.split, morphism.splitBack⟩

namespace SplitMorphism

variable {Source : Type u} {Target : Type v} {S : NativeStructure Source} {T : NativeStructure Target}
  (morphism : SplitMorphism S T)

/-- Environments related by preimage: the source's sets are the preimages of the target's. -/
def EnvPreimage {n : ℕ} (sourceEnv : Env Source n) (targetEnv : Env Target n) : Prop :=
  ∀ index element, element ∈ sourceEnv index ↔ morphism.map element ∈ targetEnv index

theorem EnvPreimage.extend {n : ℕ} {sourceEnv : Env Source n} {targetEnv : Env Target n}
    (related : morphism.EnvPreimage sourceEnv targetEnv) (set : Set Target) :
    morphism.EnvPreimage (sourceEnv.extend (morphism.map ⁻¹' set)) (targetEnv.extend set) := by
  intro index element
  refine Fin.cases ?_ (fun index' => ?_) index
  · exact Iff.rfl
  · exact related index' element

/-- **Along a split morphism, a formula of steps and splits holds at an element exactly when it holds at its
image.** -/
theorem sat_iff : ∀ {n : ℕ} (formula : Formula n), formula.splitForward = true →
    ∀ {sourceEnv : Env Source n} {targetEnv : Env Target n}, morphism.EnvPreimage sourceEnv targetEnv →
      ∀ element, S.sat sourceEnv formula element ↔ T.sat targetEnv formula (morphism.map element)
  | _, .top, _, _, _, _, _ => Iff.rfl
  | _, .bot, _, _, _, _, _ => Iff.rfl
  | _, .and left right, forward, _, _, related, element => by
    simp only [Formula.splitForward, Bool.and_eq_true] at forward
    exact and_congr (sat_iff left forward.1 related element) (sat_iff right forward.2 related element)
  | _, .or left right, forward, _, _, related, element => by
    simp only [Formula.splitForward, Bool.and_eq_true] at forward
    exact or_congr (sat_iff left forward.1 related element) (sat_iff right forward.2 related element)
  | _, .var index, _, _, _, related, element => related index element
  | _, .mu inner, forward, sourceEnv, targetEnv, related, element => by
    simp only [Formula.splitForward] at forward
    constructor
    · intro holds closed closedHolds
      exact holds (morphism.map ⁻¹' closed) fun other otherHolds =>
        closedHolds _ ((sat_iff inner forward (related.extend morphism closed) other).mp otherHolds)
    · intro holds closed closedHolds
      let pushed : Set Target := {image | ∀ origin, morphism.map origin = image → origin ∈ closed}
      have inside : ∀ origin, morphism.map origin ∈ pushed → origin ∈ closed :=
        fun origin member => member origin rfl
      have pushedHolds := holds pushed fun image imageHolds origin originMaps => by
        subst originMaps
        exact closedHolds origin (S.sat_mono inner (sourceEnv.extend_sub fun other member => inside other member) origin
          ((sat_iff inner forward (related.extend morphism pushed) origin).mpr imageHolds))
      exact inside element pushedHolds
  | _, .nu inner, forward, sourceEnv, targetEnv, related, element => by
    simp only [Formula.splitForward] at forward
    constructor
    · rintro ⟨invariant, member, preserved⟩
      refine ⟨morphism.map '' invariant, ⟨element, member, rfl⟩, ?_⟩
      rintro _ ⟨other, otherMember, rfl⟩
      exact (sat_iff inner forward (related.extend morphism (morphism.map '' invariant)) other).mp
        (S.sat_mono inner (sourceEnv.extend_sub fun origin inside => Set.mem_image_of_mem morphism.map inside) other
          (preserved other otherMember))
    · rintro ⟨invariant, member, preserved⟩
      exact ⟨morphism.map ⁻¹' invariant, member, fun other otherMember =>
        (sat_iff inner forward (related.extend morphism invariant) other).mpr (preserved _ otherMember)⟩
  | _, .possibly _ formula, forward, _, _, related, element => by
    simp only [Formula.splitForward, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at forward
    constructor
    · rintro ⟨next, step, holds⟩
      exact ⟨morphism.map next, morphism.step forward.1 step, (sat_iff formula forward.2 related next).mp holds⟩
    · rintro ⟨next', step', holds'⟩
      obtain ⟨next, step, rfl⟩ := morphism.stepBack forward.1 step'
      exact ⟨next, step, (sat_iff formula forward.2 related next).mpr holds'⟩
  | _, .necessarily _ formula, forward, _, _, related, element => by
    simp only [Formula.splitForward, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at forward
    constructor
    · intro every next' step'
      obtain ⟨next, step, rfl⟩ := morphism.stepBack forward.1 step'
      exact (sat_iff formula forward.2 related next).mp (every next step)
    · intro every next step
      exact (sat_iff formula forward.2 related next).mpr (every _ (morphism.step forward.1 step))
  | _, .split _ left right, forward, _, _, related, element => by
    simp only [Formula.splitForward, Bool.and_eq_true] at forward
    constructor
    · rintro ⟨first, second, isSplit, firstHolds, secondHolds⟩
      exact ⟨morphism.map first, morphism.map second, morphism.split isSplit,
        (sat_iff left forward.1 related first).mp firstHolds, (sat_iff right forward.2 related second).mp secondHolds⟩
    · rintro ⟨first', second', isSplit', firstHolds, secondHolds⟩
      obtain ⟨first, second, isSplit, rfl, rfl⟩ := morphism.splitBack isSplit'
      exact ⟨first, second, isSplit, (sat_iff left forward.1 related first).mpr firstHolds,
        (sat_iff right forward.2 related second).mpr secondHolds⟩
  | _, .everySplit _ left right, forward, _, _, related, element => by
    simp only [Formula.splitForward, Bool.and_eq_true] at forward
    constructor
    · intro every first' second' isSplit'
      obtain ⟨first, second, isSplit, rfl, rfl⟩ := morphism.splitBack isSplit'
      exact (every first second isSplit).imp (sat_iff left forward.1 related first).mp
        (sat_iff right forward.2 related second).mp
    · intro every first second isSplit
      exact (every _ _ (morphism.split isSplit)).imp (sat_iff left forward.1 related first).mpr
        (sat_iff right forward.2 related second).mpr
  | _, .sometimeBefore _ _, forward, _, _, _, _ | _, .alwaysBefore _ _, forward, _, _, _, _
  | _, .atLeast _ _ _ _, forward, _, _, _, _ | _, .allButFewer _ _ _ _, forward, _, _, _, _
  | _, .built _ _, forward, _, _, _, _ | _, .everyBuilt _ _, forward, _, _, _, _
  | _, .empty _, forward, _, _, _, _ | _, .nonEmpty _, forward, _, _, _, _
  | _, .single _ _, forward, _, _, _, _ | _, .everySingle _ _, forward, _, _, _, _
  | _, .body _, forward, _, _, _, _ | _, .everyBody _, forward, _, _, _, _
  | _, .multiBody _ _, forward, _, _, _, _ | _, .everyMultiBody _ _, forward, _, _, _, _
  | _, .bound _, forward, _, _, _, _ | _, .notBound _, forward, _, _, _, _
  | _, .typed _, forward, _, _, _, _ | _, .untyped _, forward, _, _, _, _
  | _, .is _, forward, _, _, _, _ | _, .isNot _, forward, _, _, _, _
  | _, .mapsAll _ _, forward, _, _, _, _ | _, .mapsSome _ _, forward, _, _, _, _
  | _, .someOf _ _, forward, _, _, _, _ | _, .everyOf _ _, forward, _, _, _, _
  | _, .inRelation _, forward, _, _, _, _ | _, .notInRelation _, forward, _, _, _, _ => by
    simp [Formula.splitForward] at forward

end SplitMorphism

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
