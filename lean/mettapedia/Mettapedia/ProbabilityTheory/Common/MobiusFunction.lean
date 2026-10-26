import Mettapedia.Order.FiniteIncidence
import Mathlib.Tactic

/-!
# Finite Möbius coefficients and inversion

The independently defined interval recurrence agrees with Mathlib's incidence
algebra coefficient. Its two cancellation laws therefore share Mathlib's proof;
integer zeta and Möbius transforms specialize the common finite transform.
The final Catalan coefficient sequence is a formula, not a proof identifying
it with the Möbius function of a separately constructed noncrossing lattice.
-/

namespace Mettapedia.ProbabilityTheory.Common
open Finset
open scoped BigOperators
open Mettapedia.Order

section FinitePoset
variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]
local instance : DecidableLT P := fun a b =>
  decidable_of_iff (a ≤ b ∧ a ≠ b) lt_iff_le_and_ne.symm
local instance : LocallyFiniteOrder P := Fintype.toLocallyFiniteOrder

def closedInterval (x y : P) : Finset P := univ.filter (fun z => x ≤ z ∧ z ≤ y)
def halfOpenInterval (x y : P) : Finset P := univ.filter (fun z => x ≤ z ∧ z ≤ y ∧ z ≠ y)

namespace closedInterval
omit [DecidableEq P] in
@[simp] theorem mem_iff (x y z : P) : z ∈ closedInterval x y ↔ x ≤ z ∧ z ≤ y := by
  simp [closedInterval]
omit [DecidableEq P] in
theorem self_mem_of_le {x y : P} (h : x ≤ y) : x ∈ closedInterval x y := by simp [h]
omit [DecidableEq P] in
theorem self_mem_right_of_le {x y : P} (h : x ≤ y) : y ∈ closedInterval x y := by simp [h]
omit [DecidableEq P] in
@[simp] theorem singleton_eq {x : P} : closedInterval x x = {x} := by
  ext z; simp [closedInterval, le_antisymm_iff, and_comm]
end closedInterval

namespace halfOpenInterval
@[simp] theorem mem_iff (x y z : P) : z ∈ halfOpenInterval x y ↔ x ≤ z ∧ z ≤ y ∧ z ≠ y := by
  simp [halfOpenInterval]
@[simp] theorem singleton_empty {x : P} : halfOpenInterval x x = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  rw [mem_iff] at hz
  exact hz.2.2 (le_antisymm hz.2.1 hz.1)
theorem not_mem_right (x y : P) : y ∉ halfOpenInterval x y := by simp
end halfOpenInterval

theorem closedInterval_eq_Icc (x y : P) : closedInterval x y = Icc x y := by ext; simp
theorem halfOpenInterval_eq_Ico (x y : P) : halfOpenInterval x y = Ico x y := by
  ext; simp [lt_iff_le_and_ne]

def intervalCard (x y : P) : ℕ := (closedInterval x y).card

theorem intervalCard_lt_of_mem_halfOpen {x y z : P} (hle : x ≤ y)
    (hz : z ∈ halfOpenInterval x y) : intervalCard x z < intervalCard x y := by
  rw [halfOpenInterval.mem_iff] at hz
  unfold intervalCard
  apply card_lt_card
  refine ⟨?_, ?_⟩
  · intro w hw
    rw [closedInterval.mem_iff] at hw ⊢
    exact ⟨hw.1, le_trans hw.2 hz.2.1⟩
  · intro subset
    have bad := (closedInterval.mem_iff _ _ _).mp (subset (closedInterval.self_mem_right_of_le hle))
    exact hz.2.2 (le_antisymm hz.2.1 bad.2)

noncomputable def mobius : P → P → ℤ
  | x, y =>
    if hxy : x = y then 1
    else if hle : x ≤ y then
      -((halfOpenInterval x y).attach.sum fun ⟨z, hz⟩ =>
          have : intervalCard x z < intervalCard x y := intervalCard_lt_of_mem_halfOpen hle hz
          mobius x z)
    else 0
termination_by x y => intervalCard x y

namespace mobius
@[simp] theorem diag (x : P) : mobius x x = 1 := by rw [mobius]; simp

theorem eq_zero_of_not_le {x y : P} (h : ¬x ≤ y) : mobius x y = 0 := by
  rw [mobius]; simp [h, show x ≠ y from fun eq => h (eq ▸ le_refl x)]

theorem unfold_of_ne_le {x y : P} (hne : x ≠ y) (hle : x ≤ y) :
    mobius x y = -((halfOpenInterval x y).attach.sum fun ⟨z, _⟩ => mobius x z) := by
  conv_lhs => rw [mobius]
  simp [hne, hle]

theorem attach_sum_eq (x y : P) :
    (halfOpenInterval x y).attach.sum (fun ⟨z, _⟩ => mobius x z) =
    (halfOpenInterval x y).sum (fun z => mobius x z) := Finset.sum_attach _ _
end mobius

/-- Equality follows from the independently authored recurrence, not from an alias. -/
theorem mobius_eq_mu (x y : P) : mobius x y = IncidenceAlgebra.mu ℤ x y := by
  have aux : ∀ n, ∀ x y : P, intervalCard x y = n → mobius x y = IncidenceAlgebra.mu ℤ x y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y card
      by_cases equal : x = y
      · subst y; simp
      by_cases le : x ≤ y
      · rw [mobius.unfold_of_ne_le equal le, mobius.attach_sum_eq,
          IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne equal, ← halfOpenInterval_eq_Ico]
        congr 1
        apply sum_congr rfl
        intro z hz
        exact ih _ (card ▸ intervalCard_lt_of_mem_halfOpen le hz) x z rfl
      · rw [mobius.eq_zero_of_not_le le, IncidenceAlgebra.apply_eq_zero_of_not_le le]
  exact aux _ x y rfl

namespace mobius

theorem sum_closedInterval_eq_ite (x y : P) (_hle : x ≤ y) :
    (closedInterval x y).sum (fun z => mobius x z) = if x = y then 1 else 0 := by
  simpa only [closedInterval_eq_Icc, mobius_eq_mu] using IncidenceAlgebra.sum_Icc_mu_right (𝕜 := ℤ) x y

theorem sum_eq_one_iff_diag {x y : P} (hle : x ≤ y) :
    (closedInterval x y).sum (fun z => mobius x z) = 1 ↔ x = y := by
  rw [sum_closedInterval_eq_ite x y hle]; simp

theorem sum_eq_zero_iff_ne {x y : P} (hle : x ≤ y) :
    (closedInterval x y).sum (fun z => mobius x z) = 0 ↔ x ≠ y := by
  rw [sum_closedInterval_eq_ite x y hle]; simp

theorem sum_closedInterval_second_eq_ite (x y : P) (_hle : x ≤ y) :
    (closedInterval x y).sum (fun z => mobius z y) = if x = y then 1 else 0 := by
  simpa only [closedInterval_eq_Icc, mobius_eq_mu] using IncidenceAlgebra.sum_Icc_mu_left (𝕜 := ℤ) x y
end mobius

noncomputable def zetaTransform (f : P → ℤ) (y : P) : ℤ := FiniteIncidence.lowerSum f y
noncomputable def mobiusTransform (g : P → ℤ) (y : P) : ℤ :=
  FiniteIncidence.lowerSum (fun x => mobius x y * g x) y

omit [DecidableEq P] in
theorem filter_le_le_eq_closedInterval (w y : P) :
    univ.filter (fun x => w ≤ x ∧ x ≤ y) = closedInterval w y := rfl

theorem mobiusTransform_eq_inverse (g : P → ℤ) : mobiusTransform g = FiniteIncidence.inverse g := by
  funext y
  simp only [mobiusTransform, mobius_eq_mu, FiniteIncidence.inverse_apply]

theorem mobius_inversion (f : P → ℤ) (y : P) : mobiusTransform (zetaTransform f) y = f y := by
  rw [mobiusTransform_eq_inverse]
  exact congrFun (FiniteIncidence.inverse_lowerSum f) y
end FinitePoset

/-- Explicit Catalan coefficients; identifying their lattice interpretation is separate. -/
def mobiusNC : ℕ → ℤ
  | 0 => 1  -- Convention for empty case
  | n + 1 => (-1 : ℤ) ^ n * (Nat.choose (2 * n) n / (n + 1))

theorem mobiusNC_zero : mobiusNC 0 = 1 := rfl

theorem mobiusNC_one : mobiusNC 1 = 1 := by decide

theorem mobiusNC_two : mobiusNC 2 = -1 := by decide

theorem mobiusNC_three : mobiusNC 3 = 2 := by decide

theorem mobiusNC_four : mobiusNC 4 = -5 := by decide


end Mettapedia.ProbabilityTheory.Common
