import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-! Squared derivative cost of a common gate multiplying a finite scalar partition. -/

set_option autoImplicit false

namespace Mettapedia.Analysis.ScaledPartitionDerivative

theorem sum_deriv_mul_sq_le {ι : Type*} (S : Finset ι)
    {a : ℝ → ℝ} {ad : ℝ} {p : ι → ℝ → ℝ} {pd : ι → ℝ} {t : ℝ}
    (ha : HasDerivAt a ad t) (hp : ∀ i ∈ S, HasDerivAt (p i) (pd i) t) :
    (∑ i ∈ S, deriv (fun s ↦ a s * p i s) t ^ 2) ≤
      2 * ad ^ 2 * (∑ i ∈ S, p i t ^ 2) + 2 * a t ^ 2 * ∑ i ∈ S, pd i ^ 2 := by
  calc
    _ ≤ ∑ i ∈ S, (2 * ad ^ 2 * p i t ^ 2 + 2 * a t ^ 2 * pd i ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [(ha.fun_mul (hp i hi)).deriv]
      nlinarith only [sq_nonneg (ad * p i t - a t * pd i)]
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

end Mettapedia.Analysis.ScaledPartitionDerivative
