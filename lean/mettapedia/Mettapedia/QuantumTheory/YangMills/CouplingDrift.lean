import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The one-loop drift of the lattice coupling

v14 writes the flow of the lattice coupling `β = 2N/g²` under one block step of
factor `b` as `β_{j+1} = β_j - 4 N b₀ log b + E_j`, with `b₀ = 11/(3·16π²)`,
and states that this matches the one-loop beta function
`μ dg/dμ = -b₀ N g³`.  Under exactly those conventions `μ dβ/dμ = 4 N² b₀`
wherever `g ≠ 0`, so along a one-loop flow `β` is affine in `log μ` and a block
step, which lowers `log μ` by `log b`, lowers `β` by exactly `4 N² b₀ log b`.
That is `N` times the displayed drift.  For `SU(2)` and `b = 2` the two values
are `0.2575…` and half of it.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace CouplingDrift

/-- The one-loop coefficient `b₀ = 11/(3·16π²)` in v14's normalization. -/
def oneLoopCoefficient : ℝ :=
  11 / (3 * 16 * Real.pi ^ 2)

/-- Under `μ dg/dμ = -b₀ N g³`, the lattice coupling `2N/g²` has logarithmic
derivative `4 N² b₀`. -/
theorem hasDerivAt_latticeCoupling (N b₀ : ℝ) {g : ℝ → ℝ} {s : ℝ}
    (hg : HasDerivAt g (-(b₀ * N * g s ^ 3)) s) (hne : g s ≠ 0) :
    HasDerivAt (fun x => 2 * N / g x ^ 2) (4 * N ^ 2 * b₀) s := by
  have hsq : HasDerivAt (fun x => g x ^ 2) (2 * g s * (-(b₀ * N * g s ^ 3))) s :=
    (hg.fun_pow 2).congr_deriv (by push_cast; ring)
  exact ((hasDerivAt_const s (2 * N)).fun_div hsq (pow_ne_zero 2 hne)).congr_deriv
    (by field_simp; ring)

/-- Along a one-loop flow, one block step of factor `b` lowers the lattice
coupling by exactly `4 N² b₀ log b`. -/
theorem latticeCoupling_blockStep (N b₀ : ℝ) {g : ℝ → ℝ}
    (hg : ∀ s, HasDerivAt g (-(b₀ * N * g s ^ 3)) s) (hne : ∀ s, g s ≠ 0)
    (s b : ℝ) :
    2 * N / g (s - Real.log b) ^ 2 =
      2 * N / g s ^ 2 - 4 * N ^ 2 * b₀ * Real.log b := by
  let shifted : ℝ → ℝ := fun x => 2 * N / g x ^ 2 - 4 * N ^ 2 * b₀ * x
  have hshifted (x : ℝ) : HasDerivAt shifted 0 x :=
    ((hasDerivAt_latticeCoupling N b₀ (hg x) (hne x)).fun_sub
      ((hasDerivAt_id x).const_mul (4 * N ^ 2 * b₀))).congr_deriv (by ring)
  have hconst := is_const_of_deriv_eq_zero
    (fun x => (hshifted x).differentiableAt) (fun x => (hshifted x).deriv)
    (s - Real.log b) s
  simp only [shifted] at hconst
  linarith

/-- The block-step drift under v14's conventions is `N` times the displayed
drift `4 N b₀ log b`. -/
theorem blockStepDrift_eq_mul_displayed (N b₀ b : ℝ) :
    4 * N ^ 2 * b₀ * Real.log b = N * (4 * N * b₀ * Real.log b) := by
  ring

/-- For `SU(2)` and `b = 2` the drift per step is `0.2575…`. -/
theorem su2_blockStepDrift_bounds :
    0.2575 < 4 * (2 : ℝ) ^ 2 * oneLoopCoefficient * Real.log 2 ∧
      4 * (2 : ℝ) ^ 2 * oneLoopCoefficient * Real.log 2 < 0.2576 := by
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have hlog_lo := Real.log_two_gt_d9
  have hlog_hi := Real.log_two_lt_d9
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsq : 0 < Real.pi ^ 2 := by positivity
  have hdrift : 4 * (2 : ℝ) ^ 2 * oneLoopCoefficient * Real.log 2 =
      11 * Real.log 2 / (3 * Real.pi ^ 2) := by
    unfold oneLoopCoefficient
    field_simp
    ring
  rw [hdrift]
  have hsq_lo : (3.141592 : ℝ) ^ 2 < Real.pi ^ 2 := by
    exact pow_lt_pow_left₀ hpi_lo (by norm_num) (by norm_num)
  have hsq_hi : Real.pi ^ 2 < (3.141593 : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ hpi_hi hpi_pos.le (by norm_num)
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith

/-- v14's displayed drift for `SU(2)` and `b = 2` is half of the drift its own
conventions give. -/
theorem su2_displayedDrift_eq_half :
    4 * (2 : ℝ) * oneLoopCoefficient * Real.log 2 =
      (4 * (2 : ℝ) ^ 2 * oneLoopCoefficient * Real.log 2) / 2 := by
  ring

#print axioms latticeCoupling_blockStep
#print axioms su2_blockStepDrift_bounds

end CouplingDrift
end YangMills
end QuantumTheory
end Mettapedia
