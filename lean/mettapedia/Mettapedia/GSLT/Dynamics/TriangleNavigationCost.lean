import Mettapedia.GSLT.Dynamics.RelationalCardinality
import Mettapedia.Machines.Cursor.AlternatingProgress
import Mettapedia.Machines.Cursor.OrderedIntersection
import Mathlib.Tactic

/-!
# Triangle navigation through alternating conditioned projections

For each admitted `(x,y)` prefix, a two-way iterator intersects the conditioned
`z` projections. Its productive advances alternate and strictly discard a key.
Combining this trace account with the triangle degree inequality bounds total
advances by twice the sum-min account, hence the squared N^(3/2) scale.

The native iterator must refine the alternating trace. Binary-seek comparison
laws, preparation, parent-prefix work, query width and output are separate
accounts. Physical occurrence products can exceed the support bound; the count
consumer handles their weights without asserting a bound on their enumeration.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.TriangleNavigationCost

open scoped BigOperators
open RelationalCardinality
open Mettapedia.Machines.Cursor.AlternatingProgress
open Mettapedia.Machines.Cursor.OrderedIntersection

variable {X Y : Type*}

theorem total_advances_le_degree_account
    (r : Finset (X × Y)) (sDegree : Y → Nat) (tDegree : X → Nat)
    (current : X × Y → Bool) (advances : X × Y → Nat)
    (traces : ∀ pair ∈ r, Execution (current pair)
      (sDegree pair.2) (tDegree pair.1) (advances pair)) :
    (∑ pair ∈ r, advances pair) ≤ 2 * triangleIntersectionWork r sDegree tDegree := by
  calc
    _ ≤ ∑ pair ∈ r, 2 * min (sDegree pair.2) (tDegree pair.1) :=
      Finset.sum_le_sum fun pair member => advances_le_twice_smaller (traces pair member)
    _ = _ := by simp [triangleIntersectionWork, Finset.mul_sum]

theorem triangle_navigation_squared_bound
    [DecidableEq X] [DecidableEq Y]
    (r : Finset (X × Y)) (xs : Finset X) (ys : Finset Y)
    (covered : r ⊆ xs ×ˢ ys) (sDegree : Y → Nat) (tDegree : X → Nat)
    (current : X × Y → Bool) (advances : X × Y → Nat)
    (traces : ∀ pair ∈ r, Execution (current pair)
      (sDegree pair.2) (tDegree pair.1) (advances pair)) :
    (∑ pair ∈ r, advances pair) ^ 2 ≤
      4 * (r.card * (∑ x ∈ xs, tDegree x) * (∑ y ∈ ys, sDegree y)) := by
  have navigation := total_advances_le_degree_account r sDegree tDegree current advances traces
  have degrees := triangle_intersection_work_sq_le r xs ys covered sDegree tDegree
  calc
    _ ≤ (2 * triangleIntersectionWork r sDegree tDegree) ^ 2 :=
      pow_le_pow_left' navigation 2
    _ = 4 * triangleIntersectionWork r sDegree tDegree ^ 2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left 4 degrees

theorem triangle_navigation_bounded_relations
    [DecidableEq X] [DecidableEq Y]
    (r : Finset (X × Y)) (xs : Finset X) (ys : Finset Y)
    (covered : r ⊆ xs ×ˢ ys) (sDegree : Y → Nat) (tDegree : X → Nat)
    (current : X × Y → Bool) (advances : X × Y → Nat)
    (traces : ∀ pair ∈ r, Execution (current pair)
      (sDegree pair.2) (tDegree pair.1) (advances pair))
    (n : Nat) (rBound : r.card ≤ n)
    (sBound : (∑ y ∈ ys, sDegree y) ≤ n)
    (tBound : (∑ x ∈ xs, tDegree x) ≤ n) :
    (∑ pair ∈ r, advances pair) ^ 2 ≤ 4 * n ^ 3 := by
  have navigation := total_advances_le_degree_account r sDegree tDegree current advances traces
  have degrees := triangle_intersection_work_bounded_relations r xs ys covered
    sDegree tDegree n rBound sBound tBound
  calc
    _ ≤ (2 * triangleIntersectionWork r sDegree tDegree) ^ 2 :=
      pow_le_pow_left' navigation 2
    _ = 4 * triangleIntersectionWork r sDegree tDegree ^ 2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left 4 degrees

/-- The algorithm-independent aggregate charges seek cost and all other work
explicitly. A native refinement supplies the actual trace and seek charges. -/
theorem charged_navigation_bound
    (r : Finset (X × Y)) (sDegree : Y → Nat) (tDegree : X → Nat)
    (current : X × Y → Bool) (advances : X × Y → Nat)
    (traces : ∀ pair ∈ r, Execution (current pair)
      (sDegree pair.2) (tDegree pair.1) (advances pair))
    (charge otherWork : Nat) :
    (∑ pair ∈ r, advances pair) * charge + otherWork ≤
      2 * triangleIntersectionWork r sDegree tDegree * charge + otherWork := by
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right charge
      (total_advances_le_degree_account r sDegree tDegree current advances traces)) otherWork

/-- Executable conditioned intersections supply their own progress trace.
No trace witness or iteration bound is assumed by this theorem. -/
theorem executable_navigation_le_degree_account
    {Key : Type*} [LinearOrder Key]
    (r : Finset (X × Y)) (s : Y → List Key) (t : X → List Key)
    (sSorted : ∀ pair ∈ r, (s pair.2).Pairwise (· < ·))
    (tSorted : ∀ pair ∈ r, (t pair.1).Pairwise (· < ·)) :
    (∑ pair ∈ r, intersectionAdvances (s pair.2) (t pair.1)) ≤
      2 * triangleIntersectionWork r (fun y => (s y).length) (fun x => (t x).length) := by
  calc
    _ ≤ ∑ pair ∈ r, 2 * min (s pair.2).length (t pair.1).length :=
      Finset.sum_le_sum fun pair member =>
        intersection_advances_le _ _ (sSorted pair member) (tSorted pair member)
    _ = _ := by simp [triangleIntersectionWork, Finset.mul_sum]

theorem executable_triangle_navigation_squared_bound
    {Key : Type*} [LinearOrder Key] [DecidableEq X] [DecidableEq Y]
    (r : Finset (X × Y)) (xs : Finset X) (ys : Finset Y)
    (covered : r ⊆ xs ×ˢ ys) (s : Y → List Key) (t : X → List Key)
    (sSorted : ∀ pair ∈ r, (s pair.2).Pairwise (· < ·))
    (tSorted : ∀ pair ∈ r, (t pair.1).Pairwise (· < ·))
    (n : Nat) (rBound : r.card ≤ n)
    (sBound : (∑ y ∈ ys, (s y).length) ≤ n)
    (tBound : (∑ x ∈ xs, (t x).length) ≤ n) :
    (∑ pair ∈ r, intersectionAdvances (s pair.2) (t pair.1)) ^ 2 ≤ 4 * n ^ 3 := by
  have navigation := executable_navigation_le_degree_account r s t sSorted tSorted
  have degrees := triangle_intersection_work_bounded_relations r xs ys covered
    (fun y => (s y).length) (fun x => (t x).length) n rBound sBound tBound
  calc
    _ ≤ (2 * triangleIntersectionWork r (fun y => (s y).length) (fun x => (t x).length)) ^ 2 :=
      pow_le_pow_left' navigation 2
    _ = 4 * triangleIntersectionWork r (fun y => (s y).length) (fun x => (t x).length) ^ 2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left 4 degrees

/-- The executable projections count the full support triangle independently
of how each intersection seeks. Occurrence weights remain a separate layer. -/
theorem executable_triangle_output_exact
    {Key : Type*} [LinearOrder Key]
    (r : Finset (X × Y)) (s : Y → List Key) (t : X → List Key)
    (sSorted : ∀ pair ∈ r, (s pair.2).Pairwise (· < ·))
    (tSorted : ∀ pair ∈ r, (t pair.1).Pairwise (· < ·)) :
    (∑ pair ∈ r, (intersectionKeys (s pair.2) (t pair.1)).length) =
      triangleCount r (fun y => (s y).toFinset) (fun x => (t x).toFinset) := by
  apply Finset.sum_congr rfl
  intro pair member
  have exactKeys := intersection_keys_exact _ _ (sSorted pair member) (tSorted pair member)
  rw [← exactKeys.2]
  exact (List.toFinset_card_of_nodup exactKeys.1.nodup).symm

/-- Repeated occurrences have a cube-sized product even at one binding tuple. -/
theorem duplicates_defeat_a_support_output_bound :
    leafMultiplicity ([[0, 0], [0, 0], [0, 0]] : List (List Nat)) = 8 ∧
      8 ^ 2 > 2 ^ 3 := by decide

end Mettapedia.GSLT.Dynamics.TriangleNavigationCost
