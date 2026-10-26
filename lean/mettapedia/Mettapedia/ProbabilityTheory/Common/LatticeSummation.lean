import Mettapedia.Order.FiniteIncidence
import Mathlib.Data.Real.Basic

/-!
# Real lower-set sums

These probability-facing names specialize the generic finite incidence sum.
Order assumptions are needed only by the laws that use them; no lattice or
normalization is required merely to add entries below a query.
-/

namespace Mettapedia.ProbabilityTheory.Common
open Finset
open Mettapedia.Order

section Lower
variable {L : Type*} [LE L] [Fintype L] [DecidableLE L]

def finsetBelow (a : L) : Finset L := univ.filter (· ≤ a)
def sumBelow (f : L → ℝ) (a : L) : ℝ := ∑ x ∈ finsetBelow a, f x
def hasSingletonSupport (f : L → ℝ) (x : L) : Prop := ∀ y, y ≠ x → f y = 0

def totalSum (f : L → ℝ) : ℝ := ∑ x, f x

@[simp] theorem finsetBelow.mem_iff (a x : L) : x ∈ finsetBelow a ↔ x ≤ a := by
  simp [finsetBelow]

theorem sumBelow.add (f g : L → ℝ) (a : L) :
    sumBelow (f + g) a = sumBelow f a + sumBelow g a := FiniteIncidence.lowerSum_add f g a

theorem sumBelow.smul (f : L → ℝ) (c : ℝ) (a : L) :
    sumBelow (c • f) a = c * sumBelow f a := by
  simp [sumBelow, mul_sum]

theorem sumBelow.nonneg_of_nonneg (f : L → ℝ) (hf : ∀ x, 0 ≤ f x) (a : L) :
    0 ≤ sumBelow f a := sum_nonneg fun x _ => hf x

namespace hasSingletonSupport
variable {f : L → ℝ} {x : L}
theorem sumBelow_eq [DecidableEq L] (hf : hasSingletonSupport f x) (a : L) :
    sumBelow f a = if x ≤ a then f x else 0 := by
  change (∑ y ∈ FiniteIncidence.lowerSet a, f y) = _
  calc
    _ = ∑ y ∈ FiniteIncidence.lowerSet a, if y = x then f x else 0 := by
      apply sum_congr rfl
      intro y _
      by_cases equal : y = x
      · simp [equal]
      · rw [hf y equal, if_neg equal]
    _ = _ := by simp
end hasSingletonSupport
end Lower

section Ordered
variable {L : Type*} [PartialOrder L] [Fintype L] [DecidableLE L] [DecidableEq L]

omit [DecidableEq L] in
theorem finsetBelow.subset_of_le {a b : L} (h : a ≤ b) : finsetBelow a ⊆ finsetBelow b :=
  fun _ hx => (finsetBelow.mem_iff _ _).mpr (le_trans ((finsetBelow.mem_iff _ _).mp hx) h)

omit [DecidableEq L] in
@[simp] theorem finsetBelow.self_mem (a : L) : a ∈ finsetBelow a := by simp

omit [DecidableEq L] in
@[simp] theorem finsetBelow.bot_eq_singleton [OrderBot L] : finsetBelow (⊥ : L) = {⊥} := by
  ext; simp [le_bot_iff]

omit [DecidableEq L] in
@[simp] theorem finsetBelow.top_eq_univ [OrderTop L] : finsetBelow (⊤ : L) = univ := by ext; simp

omit [DecidableEq L] in
@[simp] theorem finsetBelow.bot_mem [OrderBot L] (a : L) : ⊥ ∈ finsetBelow a := by simp

omit [DecidableEq L] in
@[simp] theorem sumBelow.bot [OrderBot L] (f : L → ℝ) : sumBelow f ⊥ = f ⊥ := by
  change ∑ x ∈ finsetBelow (⊥ : L), f x = f ⊥
  simp

omit [DecidableEq L] in
@[simp] theorem sumBelow.top [OrderTop L] (f : L → ℝ) : sumBelow f ⊤ = ∑ x, f x := by
  change ∑ x ∈ finsetBelow (⊤ : L), f x = ∑ x, f x
  simp

omit [DecidableEq L] in
theorem sumBelow.mono_of_nonneg (f : L → ℝ) (hf : ∀ x, 0 ≤ f x) {a b : L} (hab : a ≤ b) :
    sumBelow f a ≤ sumBelow f b :=
  sum_le_sum_of_subset_of_nonneg (finsetBelow.subset_of_le hab) (fun x _ _ => hf x)

omit [DecidableEq L] in
theorem sumBelow.self_le_of_nonneg (f : L → ℝ) (hf : ∀ x, 0 ≤ f x) (a : L) :
    f a ≤ sumBelow f a := single_le_sum (fun x _ => hf x) (finsetBelow.self_mem a)

omit [DecidableEq L] in
theorem sumBelow.bot_le_of_nonneg [OrderBot L] (f : L → ℝ) (hf : ∀ x, 0 ≤ f x) (a : L) :
    f ⊥ ≤ sumBelow f a := single_le_sum (fun x _ => hf x) (finsetBelow.bot_mem a)

theorem hasSingletonSupport.sumBelow_eq_total_iff [OrderTop L] {f : L → ℝ} {x : L}
    (hf : hasSingletonSupport f x) (hfx : f x ≠ 0) (a : L) :
    sumBelow f a = sumBelow f ⊤ ↔ x ≤ a := by
  rw [hf.sumBelow_eq, hf.sumBelow_eq]; simp only [le_top, ↓reduceIte]
  split_ifs <;> simp_all [ne_comm]

theorem hasSingletonSupport.sumBelow_lt_total_of_not_le [OrderTop L] {f : L → ℝ} {x : L}
    (hf : hasSingletonSupport f x) (hfx : 0 < f x) {a : L} (hna : ¬x ≤ a) :
    sumBelow f a < sumBelow f ⊤ := by
  rw [hf.sumBelow_eq, hf.sumBelow_eq]; simpa [hna] using hfx

omit [DecidableEq L] in
theorem totalSum_eq_sumBelow_top [OrderTop L] (f : L → ℝ) : totalSum f = sumBelow f ⊤ := by
  simp [totalSum]
end Ordered
end Mettapedia.ProbabilityTheory.Common
