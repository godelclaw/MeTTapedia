import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Sparse decomposition of additive premise scores

The dense reference visits every candidate-feature pair.  Its sparse
realization starts with the score for every feature being absent, then visits
only the observed postings and adds their corrections.  The first theorem is
parametric in the coefficient ring: logarithms and learned weights have
already been evaluated before this additive identity is used.

Runtime floating-point evaluation is a separate realization obligation.  In
particular, the implementation retains a declared contribution order and is
tested against the dense binary64 reference; this exact algebraic theorem does
not assert associativity of floating-point addition.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Retrieval.SparseBayes

open scoped BigOperators

variable {Feature R : Type*} [CommRing R]

def denseTerm (weight hit : Feature → R) (observed : Feature → Bool)
    (penalty : R) (feature : Feature) : R :=
  if observed feature then weight feature * hit feature
  else weight feature * penalty

def correction (weight hit : Feature → R) (observed : Feature → Bool)
    (penalty : R) (feature : Feature) : R :=
  if observed feature then weight feature * (hit feature - penalty) else 0

theorem sparse_sum (features : Finset Feature) (penalty : R)
    (weight hit : Feature → R) (observed : Feature → Bool) :
    (∑ feature ∈ features, denseTerm weight hit observed penalty feature) =
      penalty * (∑ feature ∈ features, weight feature) +
      ∑ feature ∈ features, correction weight hit observed penalty feature := by
  classical
  induction features using Finset.induction_on with
  | empty => simp
  | @insert feature rest absent ih =>
      simp only [Finset.sum_insert absent]
      rw [ih]
      cases h : observed feature <;>
        simp [denseTerm, correction, h] <;> ring

theorem sparse_decomposition (features : Finset Feature) (base penalty : R)
    (weight hit : Feature → R) (observed : Feature → Bool) :
    base + ∑ feature ∈ features, denseTerm weight hit observed penalty feature =
      base + penalty * (∑ feature ∈ features, weight feature) +
        ∑ feature ∈ features, correction weight hit observed penalty feature := by
  rw [sparse_sum]
  ring

theorem correction_eq_filtered_sum (features : Finset Feature) (penalty : R)
    (weight hit : Feature → R) (observed : Feature → Bool) :
    (∑ feature ∈ features, correction weight hit observed penalty feature) =
      ∑ feature ∈ features.filter (observed ·),
        weight feature * (hit feature - penalty) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro feature member
  cases h : observed feature <;> simp [correction, h]

theorem sparse_filtered_decomposition (features : Finset Feature)
    (base penalty : R) (weight hit : Feature → R)
    (observed : Feature → Bool) :
    base + ∑ feature ∈ features, denseTerm weight hit observed penalty feature =
      base + penalty * (∑ feature ∈ features, weight feature) +
        ∑ feature ∈ features.filter (observed ·),
          weight feature * (hit feature - penalty) := by
  rw [sparse_decomposition, correction_eq_filtered_sum]

/-! Source positions are retained as occurrences.  Filtering a list therefore
counts repeated evidence and excludes the query and every later source. -/

def prefixCount (sources : List Nat) (cutoff : Nat) : Nat :=
  (sources.filter (· < cutoff)).length

theorem prefixCount_append_later (sources : List Nat) (cutoff later : Nat)
    (notBefore : cutoff ≤ later) :
    prefixCount (sources ++ [later]) cutoff = prefixCount sources cutoff := by
  simp [prefixCount, Nat.not_lt.mpr notBefore]

theorem prefixCount_duplicate_before (sources : List Nat) (cutoff source : Nat)
    (before : source < cutoff) :
    prefixCount (sources ++ [source, source]) cutoff =
      prefixCount sources cutoff + 2 := by
  simp [prefixCount, before]

example :
    denseTerm (fun _ : Unit => (2 : Int)) (fun _ => 7)
      (fun _ => false) (-4) () = -8 := by
  decide

/-- Omitting the absent-feature baseline changes the score even when there are
no nonzero postings. -/
theorem correction_only_is_not_dense :
    denseTerm (fun _ : Unit => (2 : Int)) (fun _ => 7)
        (fun _ => false) (-4) () ≠
      correction (fun _ : Unit => (2 : Int)) (fun _ => 7)
        (fun _ => false) (-4) () := by
  decide

end Mettapedia.Algorithms.Retrieval.SparseBayes
