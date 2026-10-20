import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Structural separation and certified finite decompositions

A structural declaration supplies a ternary decomposition relation independent
of its executable enumeration. Coverage compares both components modulo the
language equations. Decompositions are structural evidence, not transitions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Spatial

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe u

structure SpatialTheory (system : GSLT.{u}) where
  Split : Nat → system.Term → system.Term → system.Term → Prop
  source_equiv : ∀ {index source other left right}, system.Equiv source other →
    (Split index source left right ↔ Split index other left right)

/-- The interpretation of an empty structural catalogue. -/
def SpatialTheory.empty (system : GSLT.{u}) : SpatialTheory system where
  Split _ _ _ _ := False
  source_equiv _ := Iff.rfl

def spatialPredicate {system : GSLT.{u}} (spatial : SpatialTheory system)
    (index : Nat) (left right : EquationPredicate system) : EquationPredicate system where
  val source := ∃ first second,
    spatial.Split index source first second ∧ left first ∧ right second
  property := by
    intro source other related
    constructor
    · rintro ⟨first, second, split, holdsLeft, holdsRight⟩
      exact ⟨first, second, (spatial.source_equiv related).mp split, holdsLeft, holdsRight⟩
    · rintro ⟨first, second, split, holdsLeft, holdsRight⟩
      exact ⟨first, second, (spatial.source_equiv related).mpr split, holdsLeft, holdsRight⟩

/-- A finite implementation of the installed structural declarations. The
catalogue bit controls admission; the logical relation determines meaning. -/
structure SplitBackend (system : GSLT.{u}) (admitted : system.Term → Prop) where
  theory : SpatialTheory system
  declared : Nat → Bool
  enumerate : Nat → system.Term → List (system.Term × system.Term)
  sound : ∀ index source parts, parts ∈ enumerate index source →
    theory.Split index source parts.1 parts.2
  coverage : ∀ index source first second, theory.Split index source first second →
    ∃ parts, parts ∈ enumerate index source ∧
      system.Equiv first parts.1 ∧ system.Equiv second parts.2
  components_admitted : ∀ index source, admitted source →
    ∀ parts, parts ∈ enumerate index source → admitted parts.1 ∧ admitted parts.2

def SplitBackend.empty (system : GSLT.{u}) (admitted : system.Term → Prop) :
    SplitBackend system admitted where
  theory := .empty system
  declared _ := false
  enumerate _ _ := []
  sound _ _ _ listed := by cases listed
  coverage _ _ _ _ split := False.elim split
  components_admitted _ _ _ _ listed := by cases listed

/-- Enumerated representatives determine the independent connective because
both recursive predicates respect the language equations. -/
theorem SplitBackend.spatial_iff {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : SplitBackend system admitted) (index : Nat)
    (left right : EquationPredicate system) (source : system.Term) :
    spatialPredicate backend.theory index left right source ↔
      ∃ parts, parts ∈ backend.enumerate index source ∧ left parts.1 ∧ right parts.2 := by
  constructor
  · rintro ⟨first, second, split, holdsLeft, holdsRight⟩
    obtain ⟨parts, listed, sameLeft, sameRight⟩ := backend.coverage index source first second split
    exact ⟨parts, listed, (left.2 sameLeft).mp holdsLeft, (right.2 sameRight).mp holdsRight⟩
  · rintro ⟨parts, listed, holdsLeft, holdsRight⟩
    exact ⟨parts.1, parts.2, backend.sound index source parts listed, holdsLeft, holdsRight⟩

end Mettapedia.OSLF.NativeTypes.Decision.Spatial
