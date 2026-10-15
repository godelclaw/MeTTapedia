import Mettapedia.GSLT.Dynamics.JoinAggregation
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Signed differences of a stored-row join

A finite integer-weighted relation records multiplicity; a negative weight is
a removal delta. The join is constructed from pairs of stored rows with equal
join keys. Its bilinearity yields the exact three-term update rule, including
the interaction of the two deltas. Lifting the existing ordered list join to
weighted relations preserves its bag of answers and every duplicate count.

These laws apply to bag observations. They do not preserve enumeration order,
identify proof occurrences, admit negative multiplicities as live facts, or
establish a law for recursive fixed points. Native integer overflow, storage
representation, dependency checks and compiled-code correspondence are separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.SignedJoinDeltas

noncomputable section

abbrev Relation (Row : Type*) := Row →₀ ℤ

variable {X Y Z Row : Type*}

/-- Lift a stored list to integer multiplicities, retaining duplicate counts. -/
def ofRows : List Row → Relation Row
  | [] => 0
  | row :: rest => Finsupp.single row 1 + ofRows rest

theorem ofRows_append (first second : List Row) :
    ofRows (first ++ second) = ofRows first + ofRows second := by
  induction first with
  | nil => simp [ofRows]
  | cons row rest ih => simp [ofRows, ih, add_assoc]

section Join

variable [DecidableEq Y]

/-- One pair contributes its multiplicity product precisely when its keys match. -/
def pairContribution (left : X × Y) (right : Y × Z) (a b : ℤ) :
    Relation (X × Y × Z) :=
  if right.1 = left.2 then Finsupp.single (left.1, left.2, right.2) (a * b) else 0

@[simp] theorem pairContribution_zero_left (left : X × Y) (right : Y × Z) (b : ℤ) :
    pairContribution left right 0 b = 0 := by
  simp [pairContribution]

@[simp] theorem pairContribution_zero_right (left : X × Y) (right : Y × Z) (a : ℤ) :
    pairContribution left right a 0 = 0 := by
  simp [pairContribution]

theorem pairContribution_add_left (left : X × Y) (right : Y × Z) (a b c : ℤ) :
    pairContribution left right (a + b) c =
      pairContribution left right a c + pairContribution left right b c := by
  by_cases sameKey : right.1 = left.2 <;>
    simp [pairContribution, sameKey, add_mul, Finsupp.single_add]

theorem pairContribution_add_right (left : X × Y) (right : Y × Z) (a b c : ℤ) :
    pairContribution left right a (b + c) =
      pairContribution left right a b + pairContribution left right a c := by
  by_cases sameKey : right.1 = left.2 <;>
    simp [pairContribution, sameKey, mul_add, Finsupp.single_add]

/-- The finite-support join, with the matched key retained in the answer row. -/
def join (left : Relation (X × Y)) (right : Relation (Y × Z)) :
    Relation (X × Y × Z) :=
  left.sum fun r a => right.sum fun s b => pairContribution r s a b

@[simp] theorem join_zero_left (right : Relation (Y × Z)) :
    join (0 : Relation (X × Y)) right = 0 := by simp [join]

@[simp] theorem join_zero_right (left : Relation (X × Y)) :
    join left (0 : Relation (Y × Z)) = 0 := by simp [join]

theorem join_add_left (first second : Relation (X × Y)) (right : Relation (Y × Z)) :
    join (first + second) right = join first right + join second right := by
  unfold join
  apply Finsupp.sum_add_index'
  · intro row
    simp
  · intro row a b
    simp_rw [pairContribution_add_left]
    exact Finsupp.sum_add

theorem join_add_right (left : Relation (X × Y)) (first second : Relation (Y × Z)) :
    join left (first + second) = join left first + join left second := by
  unfold join
  simp_rw [Finsupp.sum_add_index' (fun row => pairContribution_zero_right _ row _)
    (fun row => pairContribution_add_right _ row _)]
  exact Finsupp.sum_add

/-- Negative row weights remove their joined contribution. -/
theorem join_neg_left (left : Relation (X × Y)) (right : Relation (Y × Z)) :
    join (-left) right = -join left right := by
  have balanced := join_add_left left (-left) right
  simp only [add_neg_cancel, join_zero_left] at balanced
  exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using balanced.symm)

theorem join_neg_right (left : Relation (X × Y)) (right : Relation (Y × Z)) :
    join left (-right) = -join left right := by
  have balanced := join_add_right left right (-right)
  simp only [add_neg_cancel, join_zero_right] at balanced
  exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using balanced.symm)

theorem join_sub_left (first second : Relation (X × Y)) (right : Relation (Y × Z)) :
    join (first - second) right = join first right - join second right := by
  simp [sub_eq_add_neg, join_add_left, join_neg_left]

theorem join_sub_right (left : Relation (X × Y)) (first second : Relation (Y × Z)) :
    join left (first - second) = join left first - join left second := by
  simp [sub_eq_add_neg, join_add_right, join_neg_right]

/-- Exact two-input change, not just the first-order terms. -/
def delta (left : Relation (X × Y)) (right : Relation (Y × Z))
    (changeLeft : Relation (X × Y)) (changeRight : Relation (Y × Z)) :
    Relation (X × Y × Z) :=
  join changeLeft right + join left changeRight + join changeLeft changeRight

theorem join_update (left : Relation (X × Y)) (right : Relation (Y × Z))
    (changeLeft : Relation (X × Y)) (changeRight : Relation (Y × Z)) :
    join (left + changeLeft) (right + changeRight) =
      join left right + delta left right changeLeft changeRight := by
  simp only [delta, join_add_left, join_add_right]
  abel

/-- Differencing the new join yields precisely the constructed delta. -/
theorem delta_eq_difference (left : Relation (X × Y)) (right : Relation (Y × Z))
    (changeLeft : Relation (X × Y)) (changeRight : Relation (Y × Z)) :
    delta left right changeLeft changeRight =
      join (left + changeLeft) (right + changeRight) - join left right := by
  rw [join_update]
  abel

/-- Updating the left input first gives an equivalent two-term implementation. -/
theorem delta_sequential (left : Relation (X × Y)) (right : Relation (Y × Z))
    (changeLeft : Relation (X × Y)) (changeRight : Relation (Y × Z)) :
    delta left right changeLeft changeRight =
      join changeLeft right + join (left + changeLeft) changeRight := by
  simp only [delta, join_add_left, add_assoc]

/-- Successive changes telescope to the same delta as their combined input change. -/
theorem delta_composes (left : Relation (X × Y)) (right : Relation (Y × Z))
    (firstLeft secondLeft : Relation (X × Y))
    (firstRight secondRight : Relation (Y × Z)) :
    delta left right firstLeft firstRight +
        delta (left + firstLeft) (right + firstRight) secondLeft secondRight =
      delta left right (firstLeft + secondLeft) (firstRight + secondRight) := by
  simp only [delta_eq_difference, add_assoc]
  abel

theorem join_single_single (left : X × Y) (right : Y × Z) (a b : ℤ) :
    join (Finsupp.single left a) (Finsupp.single right b) =
      pairContribution left right a b := by
  simp [join, Finsupp.sum_single_index]

/-- A single stored row joins every matching right occurrence, with multiplicity. -/
theorem join_single_ofRows (left : X × Y) (right : List (Y × Z)) :
    join (Finsupp.single left 1) (ofRows right) =
      ofRows ((right.filter fun row => row.1 = left.2).map fun row =>
        (left.1, left.2, row.2)) := by
  induction right with
  | nil => simp [ofRows]
  | cons row rest ih =>
      by_cases sameKey : row.1 = left.2 <;>
        simp [ofRows, join_add_right, join_single_single, pairContribution, sameKey, ih]

/-- The concrete weighted join is the bag observation of the existing ordered join. -/
theorem join_ofRows (left : List (X × Y)) (right : List (Y × Z)) :
    join (ofRows left) (ofRows right) =
      ofRows (JoinAggregation.join left right) := by
  induction left with
  | nil => simp [ofRows, JoinAggregation.join]
  | cons row rest ih =>
      simp only [ofRows, join_add_left, join_single_ofRows, ih,
        JoinAggregation.join, List.flatMap_cons, ofRows_append]

end Join

namespace Controls

def left : Relation (Nat × Nat) := ofRows [(1, 2), (1, 2)]
def right : Relation (Nat × Nat) := ofRows [(2, 3), (2, 3), (2, 3)]

theorem duplicate_counts_multiply : join left right (1, 2, 3) = 6 := by
  norm_num [left, right, ofRows, join_add_left, join_add_right,
    join_single_single, pairContribution, Finsupp.single_apply]

theorem removing_one_duplicate_keeps_the_other :
    join (left - Finsupp.single (1, 2) 1) right (1, 2, 3) = 3 := by
  norm_num [join_sub_left, left, right, ofRows, join_add_left, join_add_right,
    join_single_single, pairContribution, Finsupp.single_apply]

/-- Both formerly empty inputs change; omitting the cross term loses the new answer. -/
theorem first_order_terms_lose_an_answer :
    delta (0 : Relation (Nat × Nat)) (0 : Relation (Nat × Nat))
        (Finsupp.single (1, 2) 1) (Finsupp.single (2, 3) 1) (1, 2, 3) = 1 ∧
      (join (Finsupp.single (1, 2) 1) (0 : Relation (Nat × Nat)) +
        join (0 : Relation (Nat × Nat)) (Finsupp.single (2, 3) 1) :
        Relation (Nat × Nat × Nat)) (1, 2, 3) = 0 := by
  norm_num [delta, join_single_single, pairContribution, Finsupp.single_apply]

end Controls

end

end Mettapedia.GSLT.Dynamics.SignedJoinDeltas
