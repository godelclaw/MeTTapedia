import Mettapedia.ProbabilityTheory.BeliefFunctions.Basic
import Mettapedia.GSLT.Dynamics.OrderedListFold

/-!
# Ordered incidence-row execution and positivity controls

Traversal retains row occurrences and intermediate accumulators. Only complete,
duplicate-free coverage identifies its result with the mathematical transform.
Commutative addition permits reordering final sums, not identifying histories.
Transition counts measure entry visits, not native arithmetic or memory cost.
-/

namespace Mettapedia.ProbabilityTheory.BeliefFunctions.IncidenceExecution

open Finset Matrix
open Mettapedia.Order.FiniteIncidence
open Mettapedia.GSLT.Dynamics
open scoped BigOperators Matrix

section Rows
variable {P R : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P] [CommRing R]

def operation (K : IncidenceAlgebra R P) (f : P → R) (y : P) (total : R) (x : P) : R :=
  total + f x * K x y

def rowValue (K : IncidenceAlgebra R P) (f : P → R) (y : P) (rows : List P) : R :=
  rows.foldl (operation K f y) 0

omit [Fintype P] [DecidableEq P] [DecidableLE P] in
theorem rowValue_eq_sum (K : IncidenceAlgebra R P) (f : P → R) (y : P) (rows : List P) :
    rowValue K f y rows = (rows.map (fun x => f x * K x y)).sum := by
  rw [List.sum_eq_foldl, List.foldl_map]
  rfl

theorem rowValue_eq_transform (K : IncidenceAlgebra R P) (f : P → R) (y : P)
    (rows : List P) (nodup : rows.Nodup) (covers : ∀ x, x ∈ rows ↔ x ≤ y) :
    rowValue K f y rows = (f ᵥ* kernelMatrix K) y := by
  rw [rowValue_eq_sum, ← List.sum_toFinset _ nodup, Mettapedia.Order.FiniteIncidence.row_apply]
  congr 1
  ext x
  simp [covers]

theorem complete_path {S A : Type} [PartialOrder S] [Fintype S] [DecidableEq S]
    [DecidableLE S] [CommRing A] (K : IncidenceAlgebra A S) (f : S → A) (y : S)
    (rows : List S) (nodup : rows.Nodup) (covers : ∀ x, x ∈ rows ↔ x ≤ y) (result : A)
    (path : (OrderedListFold.theory (operation K f y)).RewritePath
      (.active rows (0 : A)) (.done result)) :
    result = (f ᵥ* kernelMatrix K) y ∧ path.length = rows.length + 1 := by
  obtain ⟨value, length⟩ := OrderedListFold.complete_path (operation K f y) rows (0 : A) result path
  exact ⟨value.trans (rowValue_eq_transform K f y rows nodup covers), length⟩

omit [Fintype P] [DecidableEq P] [DecidableLE P] in
theorem permuted_result (K : IncidenceAlgebra R P) (f : P → R) (y : P)
    {first second : List P} (permutation : first.Perm second) :
    rowValue K f y first = rowValue K f y second := by
  rw [rowValue_eq_sum, rowValue_eq_sum]
  exact (permutation.map _).sum_eq
end Rows

namespace Controls
open Mettapedia.ProbabilityTheory.Common
noncomputable section

/-- Integer scaling makes the complete finite fixture kernel-computable. -/
def twiceCapacity (A : Finset (Fin 3)) : ℤ :=
  if A.card ≤ 1 then 0 else if A.card = 2 then 1 else 2

def twiceMass (A : Finset (Fin 3)) : ℤ :=
  if A.card = 2 then 1 else if A.card = 3 then -1 else 0

def capacity (A : Finset (Fin 3)) : ℝ := (twiceCapacity A : ℝ) / 2
def signedMass (A : Finset (Fin 3)) : ℝ := (twiceMass A : ℝ) / 2

private theorem integer_monotone : ∀ A B : Finset (Fin 3), A ⊆ B → twiceCapacity A ≤ twiceCapacity B := by
  decide +kernel

private theorem integer_two_monotone : ∀ A B : Finset (Fin 3),
    twiceCapacity A + twiceCapacity B ≤ twiceCapacity (A ∪ B) + twiceCapacity (A ∩ B) := by
  decide +kernel

private theorem integer_cumulative : ∀ A : Finset (Fin 3),
    ∑ B ∈ A.powerset, twiceMass B = twiceCapacity A := by decide +kernel

def normalizedCapacity : NormalizedValuation (Finset (Fin 3)) where
  val := capacity
  mono A B subset := by
    have bound : (twiceCapacity A : ℝ) ≤ (twiceCapacity B : ℝ) := by
      exact_mod_cast integer_monotone A B subset
    unfold capacity
    linarith
  val_bot := by norm_num [capacity, twiceCapacity]
  val_top := by norm_num [capacity, twiceCapacity]

theorem capacity_two_monotone (A B : Finset (Fin 3)) :
    capacity A + capacity B ≤ capacity (A ∪ B) + capacity (A ∩ B) := by
  have bound : (twiceCapacity A : ℝ) + (twiceCapacity B : ℝ) ≤
      (twiceCapacity (A ∪ B) : ℝ) + (twiceCapacity (A ∩ B) : ℝ) := by
    exact_mod_cast integer_two_monotone A B
  unfold capacity
  linarith

/-- An independently authored signed assignment reconstructs the capacity. -/
theorem signed_cumulative : lowerSum signedMass = capacity := by
  funext A
  have indexing : lowerSet A = A.powerset := by ext B; simp [lowerSet]
  have sum : (∑ B ∈ A.powerset, (twiceMass B : ℝ)) = (twiceCapacity A : ℝ) := by
    exact_mod_cast integer_cumulative A
  unfold lowerSum
  rw [indexing]
  simpa only [signedMass, capacity, ← Finset.sum_div] using congrArg (fun x : ℝ => x/2) sum

theorem capacity_inverse : inverse capacity = signedMass := by
  rw [← signed_cumulative]
  exact inverse_lowerSum signedMass

theorem negative_top_mass : inverse capacity (univ : Finset (Fin 3)) = -1/2 := by
  rw [capacity_inverse]
  norm_num [signedMass, twiceMass]

/-- Even normalized 2-monotone capacities need not be belief functions. -/
theorem capacity_not_completelyMonotone : ¬ CompletelyMonotone capacity := by
  intro complete
  have positive := inverse_nonneg_of_completelyMonotone normalizedCapacity complete univ
  change 0 ≤ inverse capacity univ at positive
  rw [negative_top_mass] at positive
  norm_num at positive

theorem capacity_not_belief : ¬∃ m : BeliefFunctions.MassFunction (Fin 3), belief m = capacity := by
  intro representation
  exact capacity_not_completelyMonotone ((capacity_is_belief_iff normalizedCapacity).mp representation)

/-- Three pair-events violate the arity-three inequality, although all binary ones hold. -/
theorem triple_separation :
    let A : Finset (Fin 3) := {0,1}
    let B : Finset (Fin 3) := {0,2}
    let C : Finset (Fin 3) := {1,2}
    capacity A + capacity B + capacity C - capacity (A ∩ B) - capacity (A ∩ C) -
      capacity (B ∩ C) + capacity (A ∩ B ∩ C) = 3/2 ∧ capacity (A ∪ B ∪ C) = 1 := by
  have integer_control :
      let A : Finset (Fin 3) := {0,1}
      let B : Finset (Fin 3) := {0,2}
      let C : Finset (Fin 3) := {1,2}
      twiceCapacity A + twiceCapacity B + twiceCapacity C - twiceCapacity (A ∩ B) -
        twiceCapacity (A ∩ C) - twiceCapacity (B ∩ C) + twiceCapacity (A ∩ B ∩ C) = 3 ∧
        twiceCapacity (A ∪ B ∪ C) = 2 := by decide +kernel
  dsimp only at integer_control ⊢
  constructor
  · have casted : (twiceCapacity ({0,1} : Finset (Fin 3)) : ℝ) + twiceCapacity {0,2} +
        twiceCapacity {1,2} - twiceCapacity ({0,1} ∩ {0,2}) - twiceCapacity ({0,1} ∩ {1,2}) -
        twiceCapacity ({0,2} ∩ {1,2}) + twiceCapacity ({0,1} ∩ {0,2} ∩ {1,2}) = 3 := by
      exact_mod_cast integer_control.1
    unfold capacity
    linarith
  · unfold capacity
    rw [integer_control.2]
    norm_num

theorem belief_not_additive :
    let m := BeliefFunctions.MassFunction.singleFocal (univ : Finset (Fin 2)) Finset.univ_nonempty
    CompletelyMonotone (belief m) ∧ belief m ({0} ∪ {1}) ≠ belief m {0} + belief m {1} := by
  dsimp only
  refine ⟨belief_completelyMonotone _, ?_⟩
  have first : ¬ (univ : Finset (Fin 2)) ⊆ {0} := by decide
  have second : ¬ (univ : Finset (Fin 2)) ⊆ {1} := by decide
  have total : ({0} ∪ {1} : Finset (Fin 2)) = univ := by decide
  rw [BeliefFunctions.belief_singleFocal, BeliefFunctions.belief_singleFocal,
    BeliefFunctions.belief_singleFocal]
  norm_num [total, first, second]

theorem total_belief_loses_mass :
    let first := BeliefFunctions.MassFunction.singleFocal ({0} : Finset (Fin 2)) ⟨0,by simp⟩
    let second := BeliefFunctions.MassFunction.singleFocal ({1} : Finset (Fin 2)) ⟨1,by simp⟩
    first.m ≠ second.m ∧ belief first univ = belief second univ := by
  dsimp only
  constructor
  · intro same
    have bad := congrFun same {0}
    norm_num [BeliefFunctions.MassFunction.singleFocal] at bad
  · rw [Belief.univ, Belief.univ]

theorem duplicate_or_missing_entry :
    rowValue (IncidenceAlgebra.zeta ℤ : IncidenceAlgebra ℤ (Fin 1)) (fun _ => 1) 0 [0,0] = 2 ∧
    rowValue (IncidenceAlgebra.zeta ℤ : IncidenceAlgebra ℤ (Fin 1)) (fun _ => 1) 0 [0] = 1 ∧
    rowValue (IncidenceAlgebra.zeta ℤ : IncidenceAlgebra ℤ (Fin 1)) (fun _ => 1) 0 [] = 0 := by
  norm_num [rowValue, operation, IncidenceAlgebra.zeta_apply]

theorem prefixes_can_differ :
    let K := (IncidenceAlgebra.zeta ℤ : IncidenceAlgebra ℤ (Fin 2))
    let f := fun x : Fin 2 => if x = 0 then (1 : ℤ) else 2
    rowValue K f 1 [0,1] = rowValue K f 1 [1,0] ∧
      rowValue K f 1 [0] ≠ rowValue K f 1 [1] := by
  norm_num [rowValue, operation, IncidenceAlgebra.zeta_apply]

theorem empty_row_only_finalizes :
    (OrderedListFold.runPath
      (operation (IncidenceAlgebra.zeta ℤ : IncidenceAlgebra ℤ (Fin 1)) (fun _ => 1) 0) [] 0).length = 1 := rfl

end
end Controls
end Mettapedia.ProbabilityTheory.BeliefFunctions.IncidenceExecution
