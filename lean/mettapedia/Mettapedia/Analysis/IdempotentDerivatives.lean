import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# First and second derivatives of an idempotent

The first derivative is tangent. The second derivative has an explicit
quadratic correction; subtracting diffusion therefore does not preserve
the first-order tangent identity.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology ContDiff

namespace Mettapedia.Analysis

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem derivative_idempotent {P : ℝ → A} {D : A} {t : ℝ}
    (hP : HasDerivAt P D t) (hp : ∀ τ, P τ * P τ = P τ) :
    D * P t + P t * D = D := by
  have h := hP.mul hP
  change HasDerivAt (fun τ ↦ P τ * P τ) _ t at h
  simp_rw [hp] at h
  simpa only [add_comm] using h.unique hP

theorem second_derivative_idempotent {P : ℝ → A} {t : ℝ}
    (hP : ContDiffAt ℝ 2 P t) (hp : ∀ τ, P τ * P τ = P τ) :
    deriv (deriv P) t * P t + P t * deriv (deriv P) t +
      (2 : ℝ) • (deriv P t * deriv P t) = deriv (deriv P) t := by
  have hd := (hP.differentiableAt (by norm_num)).hasDerivAt
  have hdd := ((hP.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have h := (hdd.mul hd).add (hd.mul hdd)
  have he : deriv P =ᶠ[𝓝 t] (fun τ ↦ deriv P τ * P τ + P τ * deriv P τ) := by
    filter_upwards [hP.eventually (by norm_num)] with τ hτ
    exact (derivative_idempotent (hτ.differentiableAt (by norm_num)).hasDerivAt hp).symm
  have hsame := (h.congr_of_eventuallyEq he).unique hdd
  rw [show (2 : ℝ) • (deriv P t * deriv P t) =
    deriv P t * deriv P t + deriv P t * deriv P t by simp [two_smul]]
  convert hsame using 1
  abel

theorem parabolic_idempotent_constraint {ι : Type*} [Fintype ι]
    (P D L : A) (G : ι → A) (nu : ℝ)
    (hD : D * P + P * D = D)
    (hL : L * P + P * L + (2 : ℝ) • (∑ j, G j * G j) = L) :
    (D - nu • L) * P + P * (D - nu • L) =
      D - nu • L + (2 * nu) • (∑ j, G j * G j) := by
  rw [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
  have he : L * P + P * L = L - (2 : ℝ) • (∑ j, G j * G j) := by
    exact eq_sub_of_add_eq hL
  calc
    _ = (D * P + P * D) - nu • (L * P + P * L) := by module
    _ = _ := by rw [hD, he]; module

/-- Compressing a defective tangent identity to the image determines its
diagonal block. No symmetry or finite-dimensionality is needed. -/
theorem idempotent_defect_image_block {R : Type*} [Ring R] (P W K : R) (hP : P * P = P)
    (hW : W * P + P * W = W + K) : P * W * P = P * K * P := by
  have h := congrArg (fun X : R ↦ P * X * P) hW
  simp only [mul_add, add_mul] at h
  have hl : P * (W * P) * P = P * W * P := by simp only [mul_assoc, hP]
  have hr : P * (P * W) * P = P * W * P := by rw [← mul_assoc P P W, hP]
  rw [hl, hr] at h
  linear_combination (norm := abel) h

/-- The complementary diagonal block has the opposite sign. -/
theorem idempotent_defect_complement_block {R : Type*} [Ring R] (P W K : R) (hP : P * P = P)
    (hW : W * P + P * W = W + K) :
    (1 - P) * W * (1 - P) = -(1 - P) * K * (1 - P) := by
  have h := congrArg (fun X : R ↦ (1 - P) * X * (1 - P)) hW
  have hl : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hr : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  simp only [mul_add, add_mul, mul_assoc, hr, mul_zero] at h
  rw [← mul_assoc (1 - P) P (W * (1 - P)), hl, zero_mul] at h
  simp only [← mul_assoc, neg_mul] at h ⊢
  linear_combination (norm := abel) -h

end Mettapedia.Analysis
