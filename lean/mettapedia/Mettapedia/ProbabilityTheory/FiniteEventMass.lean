import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite event masses and branch bounds

The weights need not be normalized. These lemmas concern masses of events,
not counts of derivations or confidence. In particular the branch Fréchet
bounds remain available without a conditional-independence assumption.
-/

namespace Mettapedia.ProbabilityTheory.FiniteEventMass

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

section Additive
variable {R : Type*} [AddCommMonoid R]

noncomputable def mass (weight : Ω → R) (event : Ω → Bool) : R :=
  ∑ world, if event world then weight world else 0

theorem congr (weight : Ω → R) {first second : Ω → Bool}
    (same : ∀ world, first world = second world) : mass weight first = mass weight second :=
  congrArg (mass weight) (funext same)

/-- A Boolean observation realizes a predicate independently of its decision procedure. -/
theorem indicator (weight : Ω → R) (event : Ω → Bool) (predicate : Ω → Prop)
    [decision : DecidablePred predicate] (agrees : ∀ w, event w = true ↔ predicate w) :
    mass weight event = ∑ w, if predicate w then weight w else 0 :=
  Finset.sum_congr rfl fun w _ => if_congr (agrees w) rfl rfl

theorem nonneg [Preorder R] [IsOrderedAddMonoid R]
    (weight : Ω → R) (positive : ∀ world, 0 ≤ weight world) (event : Ω → Bool) :
    0 ≤ mass weight event :=
  Finset.sum_nonneg fun world _ => by split_ifs <;> simp_all

theorem mono [Preorder R] [IsOrderedAddMonoid R]
    (weight : Ω → R) (positive : ∀ world, 0 ≤ weight world)
    {first second : Ω → Bool} (included : ∀ world, first world = true → second world = true) :
    mass weight first ≤ mass weight second := by
  apply Finset.sum_le_sum
  intro world _
  cases left : first world <;> cases right : second world <;> simp_all

theorem partition (weight : Ω → R) (event branch : Ω → Bool) :
    mass weight event = mass weight (fun w => event w && branch w) +
      mass weight (fun w => event w && !branch w) := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun world _ => by
    cases he : event world <;> cases hb : branch world <;> simp [he, hb]

/-- Complementary events partition the total weight without subtraction. -/
theorem add_complement (weight : Ω → R) (event : Ω → Bool) :
    mass weight event + mass weight (fun w => !event w) = ∑ w, weight w := by
  simpa only [mass, Bool.true_and, if_true] using
    (partition weight (fun _ => true) event).symm

theorem mass_subtype (weight : Ω → R) (event : Ω → Prop) [DecidablePred event]
    [subtypeFintype : Fintype {w // event w}] :
    mass weight (fun w => decide (event w)) = ∑ w : {w // event w}, weight w := by
  classical
  simpa [mass, Finset.sum_filter] using
    (Finset.sum_subtype_eq_sum_filter (s := Finset.univ) (f := weight) (p := event)).symm

/-- A finite union bound needs nonnegative weights, but no normalization. -/
theorem finset_union_le {Index : Type*} [DecidableEq Index] [Preorder R] [IsOrderedAddMonoid R]
    (indices : Finset Index) (weight : Ω → R) (positive : ∀ world, 0 ≤ weight world)
    (events : Index → Ω → Bool) :
    mass weight (fun w => decide (∃ i ∈ indices, events i w = true)) ≤
      ∑ i ∈ indices, mass weight (events i) := by
  classical
  unfold mass
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun world _ => ?_
  by_cases hit : ∃ i ∈ indices, events i world = true
  · obtain ⟨i, inside, member⟩ := hit
    have contribution := Finset.single_le_sum (s := indices) (a := i)
      (f := fun j => if events j world then weight world else 0)
      (fun j _ => by split_ifs <;> simp [positive]) inside
    simpa [member, show ∃ j ∈ indices, events j world = true from ⟨i, inside, member⟩] using contribution
  · simp only [decide_eq_false hit, Bool.false_eq_true, if_false]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [positive]

theorem union_le {Index : Type*} [Fintype Index] [Preorder R] [IsOrderedAddMonoid R]
    (weight : Ω → R) (positive : ∀ world, 0 ≤ weight world) (events : Index → Ω → Bool) :
    mass weight (fun w => decide (∃ i, events i w = true)) ≤ ∑ i, mass weight (events i) := by
  classical
  exact (congr weight (fun w => decide_eq_decide.mpr (by simp))).trans_le
    (finset_union_le Finset.univ weight positive events)

/-- Disjoint events have zero common mass regardless of derivation multiplicity. -/
theorem disjoint_intersection_zero (weight : Ω → R) (first second : Ω → Bool)
    (disjoint : ∀ world, ¬ (first world = true ∧ second world = true)) :
    mass weight (fun w => first w && second w) = 0 := by
  apply Finset.sum_eq_zero
  intro world _
  cases hf : first world <;> cases hs : second world <;> simp_all
end Additive

/-- Product sampling, with no normalization or positivity requirement. -/
theorem product_event {R : Type*} [CommSemiring R] (weight : Ω → R)
    (event : Ω → Bool) (n : Nat) :
    mass (fun sample : Fin n → Ω => ∏ i, weight (sample i))
      (fun sample => decide (∀ i, event (sample i) = true)) = mass weight event ^ n := by
  unfold mass
  rw [Fintype.sum_pow]
  exact Finset.sum_congr rfl fun _ _ => by
    simp only [Finset.prod_ite_zero, Finset.mem_univ, true_implies, decide_eq_true_eq]

theorem complement (weight : Ω → ℝ) (event : Ω → Bool) :
    mass weight (fun w => !event w) = (∑ w, weight w) - mass weight event := by
  linarith [add_complement weight event]

/-- The exact interval for the common mass inside a branch carrier. -/
theorem branch_frechet (weight : Ω → ℝ) (positive : ∀ world, 0 ≤ weight world)
    (first branch second : Ω → Bool) :
    max 0 (mass weight (fun w => first w && branch w) +
        mass weight (fun w => branch w && second w) - mass weight branch) ≤
      mass weight (fun w => first w && branch w && second w) ∧
    mass weight (fun w => first w && branch w && second w) ≤
      min (mass weight (fun w => first w && branch w))
        (mass weight (fun w => branch w && second w)) := by
  constructor
  · apply max_le (nonneg weight positive _)
    unfold mass
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun w _ => by
      have := positive w
      cases hf : first w <;> cases hb : branch w <;> cases hs : second w <;> simp_all
  · exact le_min
      (mono weight positive (fun _ h => by simp_all only [Bool.and_eq_true, true_and]))
      (mono weight positive (fun _ h => by simp_all only [Bool.and_eq_true, true_and]))

/-- The signed cross-product defect vanishes exactly at the multiplicative
screening equality. This definition never divides by a possibly empty branch. -/
noncomputable def screeningDefect (weight : Ω → ℝ) (first branch second : Ω → Bool) : ℝ :=
  mass weight (fun w => first w && branch w && second w) * mass weight branch -
    mass weight (fun w => first w && branch w) * mass weight (fun w => branch w && second w)

theorem screeningDefect_eq_zero_iff (weight : Ω → ℝ) (first branch second : Ω → Bool) :
    screeningDefect weight first branch second = 0 ↔
      mass weight (fun w => first w && branch w && second w) * mass weight branch =
        mass weight (fun w => first w && branch w) * mass weight (fun w => branch w && second w) :=
  sub_eq_zero

end Mettapedia.ProbabilityTheory.FiniteEventMass
