import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# A pressure-free momentum of a linear helical parent

At a critical circle of the background circulation, the tangential and
axial linearized Euler equations give a complex momentum that only rotates.
This module checks the pressure cancellation, its scalar norm conservation,
and the coercive algebraic inequality. The derivation of the cylindrical
Euler equations and their application to a PDE solution remain analytic.
-/

namespace Mettapedia.FluidDynamics.NavierStokes.HelicalParentMomentum

open Complex

/-- Pressure cancels from `κ b - m c` at a circle where the background
axial vorticity is zero. The circle radius has been normalized to one. -/
theorem pressure_cancel (m κ Ω : ℝ) (b c p : ℂ) :
    (κ : ℂ) * (-I * m * Ω * b - I * m * p) -
      (m : ℂ) * (-I * m * Ω * c - I * κ * p) =
      -I * m * Ω * ((κ : ℂ) * b - (m : ℂ) * c) := by
  ring

/-- The tangential and axial equations imply the rotating momentum ODE. -/
theorem hasDerivAt_momentum {b c : ℝ → ℂ} {m κ Ω t : ℝ} {p : ℂ}
    (hb : HasDerivAt b (-I * m * Ω * b t - I * m * p) t)
    (hc : HasDerivAt c (-I * m * Ω * c t - I * κ * p) t) :
    HasDerivAt (fun s ↦ (κ : ℂ) * b s - (m : ℂ) * c s)
      (-I * m * Ω * ((κ : ℂ) * b t - (m : ℂ) * c t)) t := by
  convert (hb.const_mul (κ : ℂ)).sub (hc.const_mul (m : ℂ)) using 1
  · rfl
  · rfl
  · exact (pressure_cancel m κ Ω (b t) (c t) p).symm

/-- A purely rotating complex scalar has constant squared modulus locally. -/
theorem hasDerivAt_normSq_zero {q : ℝ → ℂ} {ω t : ℝ}
    (hq : HasDerivAt q (-I * ω * q t) t) :
    HasDerivAt (fun s ↦ normSq (q s)) 0 t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hq
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hq
  convert (hr.mul hr).add (hi.mul hi) using 1
  · rfl
  · rfl
  · ext s
    simp [normSq_apply]
  · simp [Complex.reCLM_apply, Complex.imCLM_apply,
      Complex.mul_re, Complex.mul_im]
    ring

/-- Global scalar ODE form. This supplies no existence theorem for a PDE. -/
theorem normSq_eq_initial {q : ℝ → ℂ} (ω : ℝ)
    (hq : ∀ t, HasDerivAt q (-I * ω * q t) t) (t : ℝ) :
    normSq (q t) = normSq (q 0) := by
  have hd (s : ℝ) := hasDerivAt_normSq_zero (hq s)
  exact is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt)
    (fun s ↦ (hd s).deriv) t 0

/-- The Gram identity behind the velocity lower bound. -/
theorem momentum_normSq_identity (m κ : ℝ) (b c : ℂ) :
    (κ ^ 2 + m ^ 2) * (normSq b + normSq c) -
        normSq ((κ : ℂ) * b - (m : ℂ) * c) =
      normSq ((m : ℂ) * b + (κ : ℂ) * c) := by
  simp [normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem momentum_normSq_le (m κ : ℝ) (b c : ℂ) :
    normSq ((κ : ℂ) * b - (m : ℂ) * c) ≤
      (κ ^ 2 + m ^ 2) * (normSq b + normSq c) := by
  have h := momentum_normSq_identity m κ b c
  have hp := normSq_nonneg ((m : ℂ) * b + (κ : ℂ) * c)
  linarith

end Mettapedia.FluidDynamics.NavierStokes.HelicalParentMomentum
