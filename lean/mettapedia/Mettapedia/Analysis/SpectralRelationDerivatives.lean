import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Differentiating an operator spectral relation

The relation `S P = μ P` is differentiated without choosing eigenvectors.
Its second derivative retains the mixed gradient term. Subtracting a sum
of spatial second derivatives from a material derivative cancels the
principal diffusion term in `S` but not this mixed term.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology ContDiff

namespace Mettapedia.Analysis.SpectralRelationDerivatives

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem derivative_relation {S P : ℝ → A} {mu : ℝ → ℝ}
    {Sdot D : A} {muRate t : ℝ}
    (hS : HasDerivAt S Sdot t) (hP : HasDerivAt P D t)
    (hmu : HasDerivAt mu muRate t) (he : ∀ τ, S τ * P τ = mu τ • P τ) :
    Sdot * P t + S t * D = muRate • P t + mu t • D := by
  have h := hS.mul hP
  change HasDerivAt (fun τ ↦ S τ * P τ) _ t at h
  simp_rw [he] at h
  simpa only [add_comm] using h.unique (hmu.smul hP)

theorem second_derivative_relation {S P : ℝ → A} {mu : ℝ → ℝ} {t : ℝ}
    (hS : ContDiffAt ℝ 2 S t) (hP : ContDiffAt ℝ 2 P t)
    (hmu : ContDiffAt ℝ 2 mu t) (he : ∀ τ, S τ * P τ = mu τ • P τ) :
    deriv (deriv S) t * P t + S t * deriv (deriv P) t +
        (2 : ℝ) • (deriv S t * deriv P t) =
      deriv (deriv mu) t • P t + mu t • deriv (deriv P) t +
        (2 * deriv mu t) • deriv P t := by
  have hSd := (hS.differentiableAt (by norm_num)).hasDerivAt
  have hPd := (hP.differentiableAt (by norm_num)).hasDerivAt
  have hmd := (hmu.differentiableAt (by norm_num)).hasDerivAt
  have hSdd := ((hS.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hPdd := ((hP.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hmdd := ((hmu.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hl := (hSdd.mul hPd).add (hSd.mul hPdd)
  have hr := (hmdd.smul hPd).add (hmd.smul hPdd)
  have he' : (fun τ ↦ deriv S τ * P τ + S τ * deriv P τ) =ᶠ[𝓝 t]
      (fun τ ↦ deriv mu τ • P τ + mu τ • deriv P τ) := by
    filter_upwards [hS.eventually (by norm_num), hP.eventually (by norm_num),
      hmu.eventually (by norm_num)] with τ hSτ hPτ hmτ
    exact derivative_relation (hSτ.differentiableAt (by norm_num)).hasDerivAt
      (hPτ.differentiableAt (by norm_num)).hasDerivAt
      (hmτ.differentiableAt (by norm_num)).hasDerivAt he
  have h := (hl.congr_of_eventuallyEq he'.symm).unique hr
  calc
    _ = _ := by convert h using 1 <;> module

/-- Algebraic cancellation of the principal spatial diffusion. The mixed
term on the right has the sign `Sⱼ Pⱼ - μⱼ Pⱼ`. -/
theorem parabolic_relation {ι : Type*} [Fintype ι]
    (S P R D LS LP : A) (SG PG : ι → A) (muRate mu LM nu : ℝ) (MG : ι → ℝ)
    (hD : (-S * S + R + nu • LS) * P + S * D = muRate • P + mu • D)
    (hL : LS * P + S * LP + (2 : ℝ) • (∑ j, SG j * PG j) =
      LM • P + mu • LP + (2 : ℝ) • (∑ j, MG j • PG j)) :
    (-S * S + R) * P + S * (D - nu • LP) =
      (muRate - nu * LM) • P + mu • (D - nu • LP) +
        (2 * nu) • (∑ j, (SG j * PG j - MG j • PG j)) := by
  have h := congrArg₂ (fun a b : A ↦ a - nu • b) hD hL
  simp only [add_mul, smul_mul_assoc, mul_sub, mul_smul_comm, Finset.sum_sub_distrib] at h ⊢
  linear_combination (norm := module) h

end Mettapedia.Analysis.SpectralRelationDerivatives
