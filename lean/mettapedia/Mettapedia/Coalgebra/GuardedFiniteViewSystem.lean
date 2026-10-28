import Mettapedia.Coalgebra.CoherentFiniteViewSystem
import Mettapedia.TypeTheory.GuardedTimeModeTheory

/-!
# Guarded coherence and global observations

Finite-view restriction is a set-valued presheaf over revision time; coherent
towers are its global sections. Compatibility with each one-tick guard generates
compatibility with every earlier revision. This is a law of observations, with
no assumed term calculus or runtime demand policy.
-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.GuardedFiniteViewSystem

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.GuardedTimeModeTheory
open Mettapedia.Coalgebra.CoherentFiniteViewSystem

universe u

/-! ## Set-valued presheaves over a mode theory -/

/-- A contravariant set-valued action of a mode theory.  A modality from a
current mode to an available mode restricts data at the current mode to data
at the available mode. -/
structure ModePresheaf (modes : ModeTheory) where
  Carrier : modes.Mode → Type u
  restrict : {current available : modes.Mode} →
    modes.Hom current available → Carrier current → Carrier available
  restrict_id : ∀ (mode : modes.Mode) (value : Carrier mode),
    restrict (modes.id mode) value = value
  restrict_comp : ∀ {first middle last : modes.Mode}
    (earlier : modes.Hom first middle) (later : modes.Hom middle last)
    (value : Carrier first),
    restrict (modes.comp earlier later) value =
      restrict later (restrict earlier value)

namespace ModePresheaf

variable {modes : ModeTheory} (presheaf : ModePresheaf.{u} modes)

/-- A compatible choice of one value at every mode. -/
structure GlobalSection where
  value : (mode : modes.Mode) → presheaf.Carrier mode
  natural : ∀ {current available : modes.Mode}
    (modality : modes.Hom current available),
    presheaf.restrict modality (value current) = value available

namespace GlobalSection

@[ext]
theorem ext {first second : presheaf.GlobalSection}
    (values : first.value = second.value) : first = second := by
  cases first
  cases second
  cases values
  rfl

end GlobalSection

end ModePresheaf

/-! ## Finite-view systems are presheaves over revision time -/

variable (system : FiniteViewSystem.{u})

/-- Restriction of finite observations is the presheaf action of guarded
revision modalities. -/
def revisionPresheaf :
    ModePresheaf.{u} revisionModes where
  Carrier := system.View
  restrict := fun modality => system.restrict modality.down
  restrict_id := system.restrict_refl
  restrict_comp := by
    intro first middle last earlier later value
    exact (system.restrict_trans later.down earlier.down value).symm

/-- A coherent finite-view tower is exactly a global section of its revision
presheaf. -/
def towerGlobalSectionEquiv :
    system.Tower ≃ (revisionPresheaf system).GlobalSection where
  toFun := fun tower =>
    { value := tower.view
      natural := fun modality => tower.coherent modality.down }
  invFun := fun global =>
    { view := global.value
      coherent := fun bounded => global.natural ⟨bounded⟩ }
  left_inv _ := FiniteViewSystem.Tower.ext _ rfl
  right_inv _ := ModePresheaf.GlobalSection.ext _ rfl

/-! ## One-tick coherence generates all coherence -/

/-- A raw family of views is locally guarded when each successor view
restricts to the preceding view along the canonical one-tick guard. -/
def GuardCoherent (system : FiniteViewSystem.{u})
    (views : (depth : Nat) → system.View depth) : Prop :=
  ∀ depth,
    (revisionPresheaf system).restrict (guard depth) (views (depth + 1)) =
      views depth

variable {system}

/-- Every globally coherent tower satisfies the local one-tick law. -/
theorem tower_guardCoherent (tower : system.Tower) :
    GuardCoherent system tower.view := by
  intro depth
  exact tower.coherent (Nat.le_succ depth)

/-- Compatibility with the one-tick guard entails compatibility with every
past-revision modality. -/
theorem coherent_of_guard
    (views : (depth : Nat) → system.View depth)
    (guarded : GuardCoherent system views)
    {earlier later : Nat} (bounded : earlier ≤ later) :
    system.restrict bounded (views later) = views earlier := by
  induction later, bounded using Nat.le_induction with
  | base =>
      exact system.restrict_refl earlier (views earlier)
  | succ later bounded inductionHypothesis =>
      exact (system.restrict_trans bounded (Nat.le_succ later) _).symm.trans
        ((congrArg (system.restrict bounded) (guarded later)).trans inductionHypothesis)

/-- A locally guarded family therefore determines a global coherent tower. -/
def towerOfGuardCoherent
    (views : (depth : Nat) → system.View depth)
    (guarded : GuardCoherent system views) : system.Tower where
  view := views
  coherent := coherent_of_guard views guarded

variable (system)

/-- Global inverse-limit coherence and local one-tick guarded coherence are
equivalent data. -/
def towerGuardCoherentEquiv :
    system.Tower ≃
      { views : (depth : Nat) → system.View depth //
        GuardCoherent system views } where
  toFun := fun tower => ⟨tower.view, tower_guardCoherent tower⟩
  invFun := fun guarded =>
    towerOfGuardCoherent guarded.1 guarded.2
  left_inv _ := FiniteViewSystem.Tower.ext _ rfl
  right_inv _ := Subtype.ext rfl

/-! ## Stream canaries -/

/-- Positive control: ordinary finite stream prefixes obey the one-tick
guard law. -/
theorem streamPrefixes_guardCoherent {Label : Type u}
    (stream : Mettapedia.Coalgebra.StreamFinality.Stream Label) :
    GuardCoherent (streamPrefixSystem Label) (fun depth =>
      Mettapedia.Coalgebra.StreamFinality.finiteView depth stream) := by
  intro depth
  exact
    Mettapedia.Coalgebra.StreamFinality.restrictPrefix_finiteView
      (Nat.le_succ depth) stream

/-- Negative control: an arbitrary raw family of finite observations need
not satisfy even the local one-tick coherence law. -/
theorem incoherentBooleanViews_not_guardCoherent :
    ¬ GuardCoherent (streamPrefixSystem Bool)
      Mettapedia.Coalgebra.CoherentPrefixTower.Tower.incoherentBooleanViews := by
  intro guarded
  have atOne := guarded 1
  exact
    Mettapedia.Coalgebra.CoherentPrefixTower.Tower.incoherentBooleanViews_violate_restriction
      atOne

end Mettapedia.Coalgebra.GuardedFiniteViewSystem
