import Mettapedia.CategoryTheory.FinitePowersetRelation

/-!
# Complete finite matching relations for weak pullbacks

Equality-kernel matching specializes the complete relation construction.
Its projections give a section of the canonical comparison. Different
correlations can share those projections, so injectivity is not inferred.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FinitePowersetWeakPullback

open FinitePowerset

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

abbrev Pair (first : X → Z) (second : Y → Z) :=
  {coordinates : X × Y // first coordinates.1 = second coordinates.2}

def first (left : X → Z) (right : Y → Z) : Pair left right → X :=
  fun pair => pair.val.1

def second (left : X → Z) (right : Y → Z) : Pair left right → Y :=
  fun pair => pair.val.2

theorem square (left : X → Z) (right : Y → Z) :
    left ∘ first left right = right ∘ second left right := funext (fun pair => pair.property)

def matching (left : X → Z) (right : Y → Z)
    (leftSuccessors : Finset X) (rightSuccessors : Finset Y) : Finset (Pair left right) :=
  FinitePowersetRelation.matching (fun value other => left value = right other)
    leftSuccessors rightSuccessors

@[simp] theorem mem_matching (left : X → Z) (right : Y → Z)
    (leftSuccessors : Finset X) (rightSuccessors : Finset Y) (pair : Pair left right) :
    pair ∈ matching left right leftSuccessors rightSuccessors ↔
      pair.val.1 ∈ leftSuccessors ∧ pair.val.2 ∈ rightSuccessors :=
  FinitePowersetRelation.mem_matching (fun value other => left value = right other)
    leftSuccessors rightSuccessors pair

/-- Two-sided equality-kernel coverage is exactly equality of direct images. -/
theorem related_iff_matching (left : X → Z) (right : Y → Z)
    (leftSuccessors : Finset X) (rightSuccessors : Finset Y) :
    Related (fun value other => left value = right other) leftSuccessors rightSuccessors ↔
      map left leftSuccessors = map right rightSuccessors := by
  classical
  simp only [le_antisymm_iff, map, Finset.image_subset_iff, Finset.mem_image, Related]
  simp only [eq_comm]

theorem matching_first (left : X → Z) (right : Y → Z)
    (leftSuccessors : Finset X) (rightSuccessors : Finset Y)
    (sameImage : map left leftSuccessors = map right rightSuccessors) :
    map (first left right) (matching left right leftSuccessors rightSuccessors) =
      leftSuccessors :=
  FinitePowersetRelation.matching_first _ _ _
    ((related_iff_matching left right _ _).mpr sameImage)

theorem matching_second (left : X → Z) (right : Y → Z)
    (leftSuccessors : Finset X) (rightSuccessors : Finset Y)
    (sameImage : map left leftSuccessors = map right rightSuccessors) :
    map (second left right) (matching left right leftSuccessors rightSuccessors) =
      rightSuccessors :=
  FinitePowersetRelation.matching_second _ _ _
    ((related_iff_matching left right _ _).mpr sameImage)

def comparison (left : X → Z) (right : Y → Z) :
    Finset (Pair left right) → Pair (map left) (map right) :=
  fun successors => ⟨(map (first left right) successors, map (second left right) successors), by
    rw [map_compose, map_compose, square]⟩

def matchingSection (left : X → Z) (right : Y → Z) :
    Pair (map left) (map right) → Finset (Pair left right) :=
  fun pair => matching left right pair.val.1 pair.val.2

theorem comparison_matching (left : X → Z) (right : Y → Z)
    (pair : Pair (map left) (map right)) :
    comparison left right (matchingSection left right pair) = pair :=
  Subtype.ext (Prod.ext (matching_first left right pair.val.1 pair.val.2 pair.property)
    (matching_second left right pair.val.1 pair.val.2 pair.property))

theorem comparison_surjective (left : X → Z) (right : Y → Z) :
    Function.Surjective (comparison left right) :=
  fun pair => ⟨matchingSection left right pair, comparison_matching left right pair⟩

end Mettapedia.CategoryTheory.FinitePowersetWeakPullback
