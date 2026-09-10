import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralResidualDepletion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StrainEigenvalueContinuity

/-!
# Quadratic generation of spectral defect

When the two transverse eigenvalues coincide initially, the spectral
gap bounds squeeze the quadratic defect coefficient to the squared
initial residual rate divided by the gap. Only a first right derivative
of the residual is required, not a second derivative of the strain.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralDefectAsymptotics

open scoped Topology RealInnerProductSpace
open Filter PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralDefectEvolution PancakeSpectralResidualDepletion StrainEigenvalueContinuity
open PancakeTopEigenvalueDerivative

local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem tendsto_norm_sq_div_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : ℝ → E) (r : E) (hd : HasDerivWithinAt z r (Set.Ici (0 : ℝ)) 0) (hz : z 0 = 0) :
    Tendsto (fun t ↦ ‖z t‖ ^ 2 / t ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (‖r‖ ^ 2)) := by
  have h := (hasDerivWithinAt_iff_tendsto_slope.mp hd).norm.pow 2
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by ext t; simp
  rw [hset] at h
  convert! h using 1
  funext t
  simp only [slope_def_module, sub_zero, hz, norm_smul, Real.norm_eq_abs,
    mul_pow, abs_inv, inv_pow, sq_abs, div_eq_mul_inv]
  ring

theorem continuous_spectralWidth : Continuous spectralWidth :=
  lipschitzWith_topEigenvalue.continuous.sub lipschitzWith_thirdEigenvalue.continuous

/-- The coincident transverse spectrum identifies the exact quadratic coefficient. -/
theorem tendsto_defect_div_sq (S : ℝ → SymmetricStrain) (w : ℝ → R3) (r : R3)
    (hS : ContinuousWithinAt S (Set.Ici (0 : ℝ)) 0)
    (hd : HasDerivWithinAt
      (fun t ↦ spectralResidual (S t).1 (topEigenvalue (S t)) (w t)) r (Set.Ici (0 : ℝ)) 0)
    (hz : spectralResidual (S 0).1 (topEigenvalue (S 0)) (w 0) = 0)
    (hg : 0 < topGap (S 0)) (hflat : spectralWidth (S 0) = topGap (S 0)) :
    Tendsto (fun t ↦ topSpectralDefect (S t) (w t) / t ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (‖r‖ ^ 2 / topGap (S 0))) := by
  let Q : ℝ → ℝ := fun t ↦ ‖spectralResidual (S t).1 (topEigenvalue (S t)) (w t)‖ ^ 2 / t ^ 2
  have hQ : Tendsto Q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (‖r‖ ^ 2)) :=
    tendsto_norm_sq_div_sq _ r hd hz
  have hSc : ContinuousWithinAt S (Set.Ioi (0 : ℝ)) 0 := hS.mono Set.Ioi_subset_Ici_self
  have hglim := continuous_topGap.continuousAt.comp_continuousWithinAt hSc
  have hwlim := continuous_spectralWidth.continuousAt.comp_continuousWithinAt hSc
  have hgpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < topGap (S t) :=
    hglim.eventually (lt_mem_nhds hg)
  have hw0 : 0 < spectralWidth (S 0) := by rw [hflat]; exact hg
  have hwpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < spectralWidth (S t) :=
    hwlim.eventually (lt_mem_nhds hw0)
  have hl := hQ.div hwlim (ne_of_gt hw0)
  dsimp only [Function.comp_apply] at hl
  rw [hflat] at hl
  have hr := hQ.div hglim (ne_of_gt hg)
  apply hl.squeeze' hr
  · filter_upwards [hwpos] with t ht
    apply (div_le_iff₀ ht).mpr
    have hb := div_le_div_of_nonneg_right
      (norm_topSpectralResidual_sq_le_width_defect (S t) (w t)) (sq_nonneg t)
    simpa only [Q, mul_div_assoc, div_mul_eq_mul_div, mul_comm] using hb
  · filter_upwards [hgpos] with t ht
    apply (le_div_iff₀ ht).mpr
    have hb := div_le_div_of_nonneg_right
      (topGap_mul_defect_le_norm_topSpectralResidual_sq (S t) (w t)) (sq_nonneg t)
    simpa only [Q, mul_div_assoc, div_mul_eq_mul_div, mul_comm] using hb

end Mettapedia.FluidDynamics.NavierStokes.SpectralDefectAsymptotics
