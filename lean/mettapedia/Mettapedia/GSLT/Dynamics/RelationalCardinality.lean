import Mathlib.Data.List.Sections
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.NormNum

/-!
# Occurrence multiplicities and triangle intersection work

An indexed assignment names one distinct binding tuple. Its matching physical
rows remain lists, so the leaf contributes their Cartesian-product cardinality.
The independent witness enumerator expands that product; the indexed consumer
multiplies lengths instead. Triangle support and the sum-min intersection account
have separate bounds. They do not bound arbitrary proof multiplicities or prove
the native iterator's operation count. Index construction, range seeks and
prefix navigation must be charged in that separate correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RelationalCardinality

open scoped BigOperators

variable {Row Assignment X Y Z : Type*}

def occurrenceProduct : List (List Row) → List (List Row)
  | [] => [[]]
  | rows :: rest => rows.flatMap fun row =>
      (occurrenceProduct rest).map (row :: ·)

def leafMultiplicity (factors : List (List Row)) : Nat :=
  (factors.map List.length).prod

theorem occurrenceProduct_length (factors : List (List Row)) :
    (occurrenceProduct factors).length = leafMultiplicity factors := by
  induction factors with
  | nil => simp [occurrenceProduct, leafMultiplicity]
  | cons rows rest ih =>
      simp only [occurrenceProduct, List.length_flatMap, List.length_map, ih,
        leafMultiplicity, List.map_cons, List.prod_cons]
      simp

def enumerateAssignments (assignments : List Assignment)
    (rowsAt : Assignment → List (List Row)) : List (Assignment × List Row) :=
  assignments.flatMap fun assignment =>
    (occurrenceProduct (rowsAt assignment)).map (assignment, ·)

def countAssignments (assignments : List Assignment)
    (rowsAt : Assignment → List (List Row)) : Nat :=
  (assignments.map fun assignment => leafMultiplicity (rowsAt assignment)).sum

/-- Every distinct assignment can publish its complete physical-row weight
instead of constructing all occurrence witnesses. The assignment domain must
still be established by the query's projection/intersection algorithm. -/
theorem countAssignments_eq_enumeration_length
    (assignments : List Assignment) (rowsAt : Assignment → List (List Row)) :
    countAssignments assignments rowsAt =
      (enumerateAssignments assignments rowsAt).length := by
  simp [countAssignments, enumerateAssignments, List.length_flatMap,
    occurrenceProduct_length]

def triangleIntersectionWork (r : Finset (X × Y))
    (sDegree : Y → Nat) (tDegree : X → Nat) : Nat :=
  ∑ pair ∈ r, min (sDegree pair.2) (tDegree pair.1)

/-- The final triangle coordinate intersects two conditioned projections.
Its sum-min account is bounded by the square root of the three relation
sizes. This squared formulation is exact in natural numbers. -/
theorem triangle_intersection_work_sq_le
    [DecidableEq X] [DecidableEq Y]
    (r : Finset (X × Y)) (xs : Finset X) (ys : Finset Y)
    (covered : r ⊆ xs ×ˢ ys)
    (sDegree : Y → Nat) (tDegree : X → Nat) :
    triangleIntersectionWork r sDegree tDegree ^ 2 ≤
      r.card * (∑ x ∈ xs, tDegree x) * (∑ y ∈ ys, sDegree y) := by
  have pointwise : ∀ pair : X × Y,
      min (sDegree pair.2) (tDegree pair.1) ^ 2 ≤
        tDegree pair.1 * sDegree pair.2 := by
    intro pair
    rw [pow_two]
    exact Nat.mul_le_mul (min_le_right _ _) (min_le_left _ _)
  have summed :
      (∑ pair ∈ r, min (sDegree pair.2) (tDegree pair.1) ^ 2) ≤
        (∑ x ∈ xs, tDegree x) * (∑ y ∈ ys, sDegree y) := by
    calc
      _ ≤ ∑ pair ∈ r, tDegree pair.1 * sDegree pair.2 :=
        Finset.sum_le_sum fun pair _ => pointwise pair
      _ ≤ ∑ pair ∈ xs ×ˢ ys, tDegree pair.1 * sDegree pair.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg covered (by intros; exact Nat.zero_le _)
      _ = _ := by
        rw [Finset.sum_product]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul]
  calc
    _ ≤ r.card * ∑ pair ∈ r, min (sDegree pair.2) (tDegree pair.1) ^ 2 := by
      exact sq_sum_le_card_mul_sum_sq
    _ ≤ r.card * ((∑ x ∈ xs, tDegree x) * (∑ y ∈ ys, sDegree y)) :=
      Nat.mul_le_mul_left _ summed
    _ = _ := by rw [Nat.mul_assoc]

theorem triangle_intersection_work_bounded_relations
    [DecidableEq X] [DecidableEq Y]
    (r : Finset (X × Y)) (xs : Finset X) (ys : Finset Y)
    (covered : r ⊆ xs ×ˢ ys) (sDegree : Y → Nat) (tDegree : X → Nat)
    (n : Nat) (rBound : r.card ≤ n)
    (sBound : (∑ y ∈ ys, sDegree y) ≤ n)
    (tBound : (∑ x ∈ xs, tDegree x) ≤ n) :
    triangleIntersectionWork r sDegree tDegree ^ 2 ≤ n ^ 3 := by
  refine (triangle_intersection_work_sq_le r xs ys covered sDegree tDegree).trans ?_
  calc
    _ ≤ (n * n) * n := Nat.mul_le_mul (Nat.mul_le_mul rBound tBound) sBound
    _ = n ^ 3 := by simp [pow_succ]

def triangleCount [DecidableEq Z] (r : Finset (X × Y))
    (s : Y → Finset Z) (t : X → Finset Z) : Nat :=
  ∑ pair ∈ r, (s pair.2 ∩ t pair.1).card

theorem triangle_count_le_intersection_work [DecidableEq Z]
    (r : Finset (X × Y)) (s : Y → Finset Z) (t : X → Finset Z) :
    triangleCount r s t ≤ triangleIntersectionWork r
      (fun y => (s y).card) (fun x => (t x).card) := by
  exact Finset.sum_le_sum fun pair _ =>
    le_min (Finset.card_le_card Finset.inter_subset_left)
      (Finset.card_le_card Finset.inter_subset_right)

namespace Controls

theorem duplicate_occurrences_multiply :
    leafMultiplicity ([[0, 0], [0, 0], [0, 0]] : List (List Nat)) = 8 := by decide

theorem support_does_not_determine_multiplicity :
    leafMultiplicity ([[0, 0], [0, 0], [0, 0]] : List (List Nat)) ≠
      leafMultiplicity [[0], [0], [0]] := by decide

theorem empty_factor_annihilates :
    leafMultiplicity ([[0, 1], [], [2, 3]] : List (List Nat)) = 0 := by decide

theorem complete_count_forgets_occurrence_order :
    leafMultiplicity ([[0, 1], [2]] : List (List Nat)) =
      leafMultiplicity [[1, 0], [2]] ∧
    occurrenceProduct ([[0, 1], [2]] : List (List Nat)) ≠
      occurrenceProduct [[1, 0], [2]] := by decide

end Controls

end Mettapedia.GSLT.Dynamics.RelationalCardinality
