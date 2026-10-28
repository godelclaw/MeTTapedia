import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Coherent finite observations

An inverse sequence has one view type at each natural-number depth. Its
coherent towers form the semantic limit. Faithfulness, completeness and
exactness concern the supplied observation map; view types need not be finite.
-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.CoherentFiniteViewSystem

universe uView uBehavior uLabel uTarget

/-- An inverse system of depth-indexed finite observations. -/
structure FiniteViewSystem where
  View : Nat → Type uView
  restrict : {earlier later : Nat} → earlier ≤ later →
    View later → View earlier
  restrict_refl : ∀ (depth : Nat) (view : View depth),
    restrict (Nat.le_refl depth) view = view
  restrict_trans : ∀ {earlier middle later : Nat}
    (earlierMiddle : earlier ≤ middle) (middleLater : middle ≤ later)
    (view : View later),
    restrict earlierMiddle (restrict middleLater view) =
      restrict (earlierMiddle.trans middleLater) view

namespace FiniteViewSystem

variable (system : FiniteViewSystem.{uView})

/-- One observation at every depth, compatible with restriction. -/
structure Tower where
  view : (depth : Nat) → system.View depth
  coherent : ∀ {earlier later : Nat} (bounded : earlier ≤ later),
    system.restrict bounded (view later) = view earlier

namespace Tower

@[ext]
theorem ext {first second : system.Tower}
    (views : first.view = second.view) : first = second := by
  cases first
  cases second
  cases views
  rfl

end Tower

/-- A levelwise observation map commuting with restriction.
Operational step preservation is a separate law. -/
structure Hom (source : FiniteViewSystem.{uView}) (target : FiniteViewSystem.{uTarget}) where
  app : (depth : Nat) → source.View depth → target.View depth
  natural : ∀ {earlier later : Nat} (bounded : earlier ≤ later) (view : source.View later),
    target.restrict bounded (app later view) = app earlier (source.restrict bounded view)

namespace Hom

variable {source : FiniteViewSystem.{uView}} {target : FiniteViewSystem.{uTarget}}
  (mapping : Hom source target)

/-- Naturality lifts finite observations to a coherent map of whole towers. -/
def mapTower (tower : source.Tower) : target.Tower where
  view depth := mapping.app depth (tower.view depth)
  coherent bounded := (mapping.natural bounded _).trans
    (congrArg (mapping.app _) (tower.coherent bounded))

theorem mapTower_injective (injective : ∀ depth, Function.Injective (mapping.app depth)) :
    Function.Injective mapping.mapTower := by
  intro first second same
  apply Tower.ext source
  funext depth
  exact injective depth (congrArg (fun tower => tower.view depth) same)

end Hom

end FiniteViewSystem

/-- A behavior supplies coherent observations at every finite depth. -/
structure BehaviorObservation
    (system : FiniteViewSystem.{uView}) (Behavior : Type uBehavior) where
  observe : (depth : Nat) → Behavior → system.View depth
  coherent : ∀ {earlier later : Nat} (bounded : earlier ≤ later)
    (behavior : Behavior),
    system.restrict bounded (observe later behavior) =
      observe earlier behavior

namespace BehaviorObservation

variable {system : FiniteViewSystem.{uView}} {Behavior : Type uBehavior}
  (observation : BehaviorObservation system Behavior)

/-- Assemble all finite observations into their coherent inverse-limit
tower. -/
def toTower (behavior : Behavior) : system.Tower where
  view depth := observation.observe depth behavior
  coherent bounded := observation.coherent bounded behavior

/-- The complete finite-view tower separates behaviors. -/
def Faithful : Prop :=
  Function.Injective observation.toTower

/-- Every coherent tower represents a behavior. -/
def Complete : Prop :=
  Function.Surjective observation.toTower

/-- Behaviors and coherent towers carry exactly the same information. -/
def Exact : Prop :=
  Function.Bijective observation.toTower

theorem exact_iff_faithful_and_complete :
    observation.Exact ↔ observation.Faithful ∧ observation.Complete :=
  Iff.rfl

/-- Exact finite-view semantics yields the corresponding equivalence. -/
noncomputable def equivalenceOfExact (exact : observation.Exact) : Behavior ≃ system.Tower :=
  Equiv.ofBijective observation.toTower exact

/-- Recode each finite observation through a restriction-compatible map. -/
def map {target : FiniteViewSystem.{uTarget}} (mapping : FiniteViewSystem.Hom system target) :
    BehaviorObservation target Behavior where
  observe depth behavior := (mapping.mapTower (observation.toTower behavior)).view depth
  coherent bounded behavior := (mapping.mapTower (observation.toTower behavior)).coherent bounded

@[simp] theorem map_toTower {target : FiniteViewSystem.{uTarget}}
    (mapping : FiniteViewSystem.Hom system target) :
    (observation.map mapping).toTower = mapping.mapTower ∘ observation.toTower := rfl

end BehaviorObservation

/-- The inverse system of finite label sequences. -/
def streamPrefixSystem (Label : Type uLabel) : FiniteViewSystem.{uLabel} where
  View depth := Fin depth → Label
  restrict bounded view index := view ⟨index.val, lt_of_lt_of_le index.isLt bounded⟩
  restrict_refl _ _ := rfl
  restrict_trans _ _ _ := rfl

end Mettapedia.Coalgebra.CoherentFiniteViewSystem
