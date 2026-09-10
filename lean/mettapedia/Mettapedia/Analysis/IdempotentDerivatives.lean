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

end Mettapedia.Analysis
