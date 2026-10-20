import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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

noncomputable def mass (weight : Ω → ℝ) (event : Ω → Bool) : ℝ :=
  ∑ world, if event world then weight world else 0

theorem congr (weight : Ω → ℝ) {first second : Ω → Bool}
    (same : ∀ world, first world = second world) : mass weight first = mass weight second := by
  congr 1
  exact funext same

theorem nonneg (weight : Ω → ℝ) (positive : ∀ world, 0 ≤ weight world) (event : Ω → Bool) :
    0 ≤ mass weight event := by
  exact Finset.sum_nonneg fun world _ => by split_ifs <;> simp_all

theorem mono (weight : Ω → ℝ) (positive : ∀ world, 0 ≤ weight world)
    {first second : Ω → Bool} (included : ∀ world, first world = true → second world = true) :
    mass weight first ≤ mass weight second := by
  apply Finset.sum_le_sum
  intro world _
  by_cases left : first world = true
  · simp [left, included world left]
  · simp only [left, Bool.false_eq_true, if_false]
    split_ifs <;> simp_all

theorem partition (weight : Ω → ℝ) (event branch : Ω → Bool) :
    mass weight event = mass weight (fun w => event w && branch w) +
      mass weight (fun w => event w && !branch w) := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro world _
  cases he : event world <;> cases hb : branch world <;> simp [he, hb]

theorem complement (weight : Ω → ℝ) (event : Ω → Bool) :
    mass weight (fun w => !event w) = (∑ w, weight w) - mass weight event := by
  have split := partition weight (fun _ => true) event
  simp only [mass, Bool.true_and, if_true] at split ⊢
  linarith

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
    have inequality : (∑ w, ((if first w && branch w then weight w else 0) +
        (if branch w && second w then weight w else 0) - (if branch w then weight w else 0))) ≤
        ∑ w, if first w && branch w && second w then weight w else 0 := by
      apply Finset.sum_le_sum
      intro world _
      have nonnegative := positive world
      cases hf : first world <;> cases hb : branch world <;> cases hs : second world <;> simp_all
    simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib, mass] using inequality
  · apply le_min
    · exact mono weight positive (fun w h => by
        simp only [Bool.and_eq_true] at h ⊢
        exact h.1)
    · exact mono weight positive (fun w h => by
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨h.1.2, h.2⟩)

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

/-- Two disjoint predicates have no common mass even if they have many
different derivations. -/
theorem disjoint_intersection_zero (weight : Ω → ℝ) (first second : Ω → Bool)
    (disjoint : ∀ world, ¬ (first world = true ∧ second world = true)) :
    mass weight (fun w => first w && second w) = 0 := by
  apply Finset.sum_eq_zero
  intro world _
  have excluded := disjoint world
  cases hf : first world <;> cases hs : second world <;> simp_all

end Mettapedia.ProbabilityTheory.FiniteEventMass
