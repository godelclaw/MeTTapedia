import Mettapedia.CategoryTheory.FinitePowersetSpan
import Mathlib.Order.Closure

/-!
# Complete finite relation spans

Two-sided coverage constructs the entire finite relation between the
supplied finite sets. Its projections are exactly those sets. The
construction retains every matching pair instead of selecting one witness
for each input, and its relation condition need not be an equality kernel.

Projection and complete matching form a Galois connection. Saturation adds all
compatible pairs between the projected supports, preserving those supports
while potentially losing the supplied correlations. It is the greatest
compatible relation with the same projections, not a decoder of the input.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FinitePowersetRelation

open FinitePowerset

universe u v

variable {X : Type u} {Y : Type v} (relation : X → Y → Prop)

abbrev Pair := {coordinates : X × Y // relation coordinates.1 coordinates.2}

def first : Pair relation → X := fun pair => pair.val.1
def second : Pair relation → Y := fun pair => pair.val.2

def matching (left : Finset X) (right : Finset Y) : Finset (Pair relation) := by
  classical
  exact (left.product right).subtype (fun coordinates => relation coordinates.1 coordinates.2)

@[simp] theorem mem_matching (left : Finset X) (right : Finset Y)
    (pair : Pair relation) :
    pair ∈ matching relation left right ↔ pair.val.1 ∈ left ∧ pair.val.2 ∈ right := by
  classical
  simp only [matching, Finset.mem_subtype]
  exact Finset.mem_product

theorem matching_first (left : Finset X) (right : Finset Y)
    (covers : Related relation left right) :
    map (first relation) (matching relation left right) = left := by
  classical
  exact Finset.image_eq_iff_surjOn_mapsTo.mpr
    ⟨fun value member => by
      obtain ⟨other, present, paired⟩ := covers.1 value member
      exact ⟨⟨(value, other), paired⟩, (mem_matching relation left right _).mpr
        ⟨member, present⟩, rfl⟩,
     fun pair member => ((mem_matching relation left right pair).mp member).1⟩

theorem matching_second (left : Finset X) (right : Finset Y)
    (covers : Related relation left right) :
    map (second relation) (matching relation left right) = right := by
  classical
  exact Finset.image_eq_iff_surjOn_mapsTo.mpr
    ⟨fun other member => by
      obtain ⟨value, present, paired⟩ := covers.2 other member
      exact ⟨⟨(value, other), paired⟩, (mem_matching relation left right _).mpr
        ⟨present, member⟩, rfl⟩,
     fun pair member => ((mem_matching relation left right pair).mp member).2⟩

/-- Any finite span gives complete coverage of both of its images. -/
theorem span_related (pairs : Finset (Pair relation)) :
    Related relation (map (first relation) pairs) (map (second relation) pairs) :=
  FinitePowersetSpan.images_related relation _ _ pairs (fun pair _ => pair.property)

theorem related_iff_span (left : Finset X) (right : Finset Y) :
    Related relation left right ↔
      ∃ pairs : Finset (Pair relation),
        map (first relation) pairs = left ∧ map (second relation) pairs = right := by
  constructor
  · intro covers
    exact ⟨matching relation left right, matching_first relation left right covers,
      matching_second relation left right covers⟩
  · rintro ⟨pairs, rfl, rfl⟩
    exact span_related relation pairs

/-- The two supports of a supplied finite relation. -/
def projections (pairs : Finset (Pair relation)) : Finset X × Finset Y :=
  (map (first relation) pairs, map (second relation) pairs)

theorem projections_matching_gc : GaloisConnection (projections relation)
    (fun supports => matching relation supports.1 supports.2) := by
  classical
  intro pairs supports
  simp only [projections, Prod.le_def, map, Finset.image_subset_iff]
  simp only [Finset.subset_iff, mem_matching, first, second, forall_and]

/-- Complete every relation-compatible pairing of the two observed supports. -/
def saturation : ClosureOperator (Finset (Pair relation)) :=
  (projections_matching_gc relation).closureOperator

@[simp] theorem projections_saturation (pairs : Finset (Pair relation)) :
    projections relation (saturation relation pairs) = projections relation pairs :=
  Prod.ext (matching_first relation _ _ (span_related relation pairs))
    (matching_second relation _ _ (span_related relation pairs))

/-- Every relation with the same supports is contained in this completion. -/
theorem saturation_greatest {pairs other : Finset (Pair relation)}
    (same : projections relation pairs = projections relation other) :
    pairs ⊆ saturation relation other :=
  (projections_matching_gc relation _ _).mp same.le

theorem saturation_eq_iff_projections_eq (pairs other : Finset (Pair relation)) :
    saturation relation pairs = saturation relation other ↔
      projections relation pairs = projections relation other := by
  refine ⟨fun same => ?_, congrArg (Function.uncurry (matching relation))⟩
  simpa only [projections_saturation] using congrArg (projections relation) same

/-- Arbitrary requested supports are recovered precisely when both are covered. -/
theorem projections_matching_eq_iff (left : Finset X) (right : Finset Y) :
    projections relation (matching relation left right) = (left, right) ↔
      Related relation left right := by
  refine ⟨fun same => (related_iff_span relation left right).mpr
    ⟨matching relation left right, congrArg Prod.fst same, congrArg Prod.snd same⟩,
    fun covers => Prod.ext (matching_first relation left right covers)
      (matching_second relation left right covers)⟩

end Mettapedia.CategoryTheory.FinitePowersetRelation
