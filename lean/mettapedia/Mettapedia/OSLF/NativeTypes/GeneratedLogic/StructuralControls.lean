import Mettapedia.OSLF.NativeTypes.GeneratedLogic.StructuralEquivalence

/-!
# Controls: structural bisimilarity

Three stuck elements, `0` and `1` built by `Nil` and `2` built by `Ok`, with no steps between them.

- **Shape is seen.** `0` and `2` are bisimilar: neither has a step or a predecessor
  (`nil_ok_bisimilar`). The first-order formula "built by `Nil`" tells them apart (`shape_separates`),
  so they are not structurally bisimilar (`nil_ok_not_structural`).
- **Copies are not.** `0` and `1` are structurally bisimilar (`nils_structural`), so they agree on every
  first-order formula (`nils_agree`), though they are distinct elements.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.StructuralControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open NativeStructure

/-- Two elements built by `Nil` and one by `Ok`, all without arguments; nothing steps. -/
def shapes : FiniteStructure (Fin 3) where
  elements := List.finRange 3
  complete := List.mem_finRange
  step _ _ _ := false
  built element constructor parts :=
    parts.isEmpty && (constructor == "Nil" && element != 2 || constructor == "Ok" && element == 2)
  split _ _ _ _ := false
  empty _ _ := false
  single _ _ _ := false
  body _ _ := false
  multiBody _ _ _ := false
  bound _ _ := false
  typed _ _ := false
  named _ _ := false
  same first second := decide (first = second)
  apply inner _ := inner
  inRelation _ _ := false

/-- Built by `Nil`. -/
def builtByNil : Formula 0 := .built "Nil" .nil

/-! ## Shape is seen -/

/-- Any relation is a bisimulation when nothing steps. -/
theorem steps_bisimulation (relation : Fin 3 → Fin 3 → Prop) : shapes.native.Bisimulation relation where
  forth := fun _ step => absurd step (by simp [shapes, FiniteStructure.native])
  back := fun _ step => absurd step (by simp [shapes, FiniteStructure.native])
  pastForth := fun _ step => absurd step (by simp [shapes, FiniteStructure.native])
  pastBack := fun _ step => absurd step (by simp [shapes, FiniteStructure.native])

theorem nil_ok_bisimilar : shapes.native.Bisimilar 0 2 := ⟨fun _ _ => True, steps_bisimulation _, trivial⟩

theorem shape_separates :
    shapes.native.sat Env.closed builtByNil 0 ∧ ¬ shapes.native.sat Env.closed builtByNil 2 :=
  ⟨(shapes.check_iff _ _).mp (by decide), fun holds => absurd ((shapes.check_iff _ _).mpr holds) (by decide)⟩

/-- **Bisimilar, yet told apart by shape.** -/
theorem nil_ok_not_structural : ¬ shapes.native.StructurallyBisimilar 0 2 := fun related =>
  shape_separates.2 (sat_of_structurallyBisimilar builtByNil rfl (Env.respects_closed _) related shape_separates.1)

/-! ## Copies are not -/

/-- The same element, or the two elements built by `Nil`. -/
def nilCopies (first second : Fin 3) : Prop := first = second ∨ (first ≠ 2 ∧ second ≠ 2)

theorem built_iff {element : Fin 3} {constructor : String} {parts : List (Fin 3)} :
    shapes.built element constructor parts = true ↔
      parts = [] ∧ (constructor = "Nil" ∧ element ≠ 2 ∨ constructor = "Ok" ∧ element = 2) := by
  simp [shapes, List.isEmpty_iff]

theorem nilCopies_not_two {first second : Fin 3} (related : nilCopies first second) : first ≠ 2 ↔ second ≠ 2 := by
  rcases related with rfl | ⟨first, second⟩
  · exact Iff.rfl
  · exact iff_of_true first second

theorem nilCopies_symm {first second : Fin 3} (related : nilCopies first second) : nilCopies second first := by
  rcases related with rfl | ⟨first, second⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨second, first⟩

theorem nilCopies_bisimulation : shapes.native.StructuralBisimulation nilCopies where
  steps := steps_bisimulation _
  builtForth := fun {first second constructor parts} related isBuilt => by
    change shapes.built first constructor parts = true at isBuilt
    rw [built_iff] at isBuilt
    obtain ⟨rfl, shape⟩ := isBuilt
    refine ⟨[], ?_, .nil⟩
    change shapes.built second constructor [] = true
    rw [built_iff]
    have same := nilCopies_not_two related
    refine ⟨rfl, ?_⟩
    rcases shape with ⟨named, notTwo⟩ | ⟨named, two⟩
    · exact Or.inl ⟨named, same.mp notTwo⟩
    · exact Or.inr ⟨named, by by_contra other; exact (same.mpr other) two⟩
  builtBack := fun {first second constructor parts'} related isBuilt => by
    change shapes.built second constructor parts' = true at isBuilt
    rw [built_iff] at isBuilt
    obtain ⟨rfl, shape⟩ := isBuilt
    refine ⟨[], ?_, .nil⟩
    change shapes.built first constructor [] = true
    rw [built_iff]
    have same := nilCopies_not_two related
    refine ⟨rfl, ?_⟩
    rcases shape with ⟨named, notTwo⟩ | ⟨named, two⟩
    · exact Or.inl ⟨named, same.mpr notTwo⟩
    · exact Or.inr ⟨named, by by_contra other; exact (same.mp other) two⟩
  splitForth := fun _ isSplit => absurd isSplit (by simp [shapes, FiniteStructure.native])
  splitBack := fun _ isSplit => absurd isSplit (by simp [shapes, FiniteStructure.native])
  singleForth := fun _ isSingle => absurd isSingle (by simp [shapes, FiniteStructure.native])
  singleBack := fun _ isSingle => absurd isSingle (by simp [shapes, FiniteStructure.native])
  bodyForth := fun _ isBody => absurd isBody (by simp [shapes, FiniteStructure.native])
  bodyBack := fun _ isBody => absurd isBody (by simp [shapes, FiniteStructure.native])
  multiBodyForth := fun _ isBody => absurd isBody (by simp [shapes, FiniteStructure.native])
  multiBodyBack := fun _ isBody => absurd isBody (by simp [shapes, FiniteStructure.native])
  empty := fun _ => Iff.rfl
  bound := fun _ => Iff.rfl
  typed := fun _ => Iff.rfl
  named := fun _ => Iff.rfl
  inRelation := fun _ => Iff.rfl

theorem nils_structural : shapes.native.StructurallyBisimilar 0 1 :=
  ⟨nilCopies, nilCopies_bisimulation, Or.inr ⟨by decide, by decide⟩⟩

/-- **Distinct copies agree on every first-order formula.** -/
theorem nils_agree : shapes.native.FirstOrderEquivalent 0 1 :=
  (firstOrderEquivalent_iff_structurallyBisimilar shapes.fullyImageFinite).mpr nils_structural

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.StructuralControls
