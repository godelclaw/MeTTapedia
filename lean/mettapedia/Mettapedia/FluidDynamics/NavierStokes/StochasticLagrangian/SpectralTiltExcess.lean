import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralSourceExcess
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LineProjectorTilt

/-!
# Absorption using only the tilt of the expanding line

For a self-adjoint source, the off-diagonal coupling is measured by
`(1-P) R P`, not the entire strain commutator. A quarter of the spectral
residual pays the absorbable part. Capping by the previous excess keeps
the collision fallback and alignment vanishing, and never increases the
cost. Measurability is obtained on the positive-gap region and its
complement, without a measurable unit eigenvector selection.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess

open scoped RealInnerProductSpace
open MeasureTheory
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution PancakeAnisotropyDepletion
open SpectralSourceCommutator SpectralDiffusionWeightLimit SpectralDiffusionExcess
open StrainEigenvalueContinuity

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def tiltNorm (S : SymmetricStrain) (R : R3 →L[ℝ] R3) : ℝ :=
  ‖(ContinuousLinearMap.id ℝ R3 - topEigenlineProjector S) * R * topEigenlineProjector S‖

theorem tiltNorm_eq (S : SymmetricStrain) (R : R3 →L[ℝ] R3) :
    tiltNorm S R = ‖lineRemainder (topVector S) (R (topVector S))‖ :=
  LineProjectorTilt.norm_transverse_projector_action R (topVector S) (topVector_norm S)

theorem tiltNorm_nonneg (S : SymmetricStrain) (R : R3 →L[ℝ] R3) : 0 ≤ tiltNorm S R := norm_nonneg _

def refinedCost (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) : ℝ :=
  max (2 * ‖R‖ - topGap S ^ 2 / 8) 0 * limitingWeight S w +
    8 * (tiltNorm S R / topGap S) ^ 2 * ‖w‖ ^ 2

def excess (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) : ℝ :=
  if 0 < topGap S then min (SpectralSourceExcess.excess S R w) (refinedCost S R w)
  else SpectralSourceExcess.excess S R w

theorem refinedCost_nonneg (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    0 ≤ refinedCost S R w := by
  have hw := limitingWeight_nonneg S w
  unfold refinedCost
  positivity

theorem excess_nonneg (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) : 0 ≤ excess S R w := by
  unfold excess
  split
  · exact le_min (SpectralSourceExcess.excess_nonneg S R w) (refinedCost_nonneg S R w)
  · exact SpectralSourceExcess.excess_nonneg S R w

theorem excess_le_previous (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    excess S R w ≤ SpectralSourceExcess.excess S R w := by
  unfold excess
  split
  · exact min_le_left _ _
  · exact le_rfl

theorem excess_le_coarse (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    excess S R w ≤ 2 * ‖R‖ * ‖w‖ ^ 2 :=
  (excess_le_previous S R w).trans (SpectralSourceExcess.excess_le_coarse S R w)

theorem abs_anisotropy_le_tilt_cost (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (hR : R.adjoint = R) (w : R3) :
    |remainderAnisotropy R (topVector S) w| ≤
      2 * ‖R‖ * limitingWeight S w + 2 * tiltNorm S R * ‖w‖ * Real.sqrt (limitingWeight S w) := by
  have h := abs_anisotropy_le_transverse S R w
  rw [hR, ← tiltNorm_eq] at h
  have hm := lineRemainder_sq_le_limitingWeight S w
  have hn : ‖lineRemainder (topVector S) w‖ ≤ Real.sqrt (limitingWeight S w) :=
    (Real.le_sqrt (norm_nonneg _) (limitingWeight_nonneg S w)).mpr hm
  have hq := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * ‖R‖)
  have htn := tiltNorm_nonneg S R
  have ht := mul_le_mul_of_nonneg_left hn
    (by positivity : 0 ≤ 2 * tiltNorm S R * ‖w‖)
  nlinarith only [h, hq, ht]

theorem tilt_cost_le_eighth_residual_add (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (w : R3) (hg : 0 < topGap S) :
    2 * tiltNorm S R * ‖w‖ * Real.sqrt (limitingWeight S w) ≤
      ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 / 8 +
        8 * (tiltNorm S R / topGap S) ^ 2 * ‖w‖ ^ 2 := by
  have hs := Real.sq_sqrt (limitingWeight_nonneg S w)
  have hq := topGap_sq_mul_limitingWeight_le_residual S w
  have hid : (topGap S * Real.sqrt (limitingWeight S w)) *
      (tiltNorm S R / topGap S * ‖w‖) = tiltNorm S R * ‖w‖ * Real.sqrt (limitingWeight S w) := by
    field_simp
  have hsq := sq_nonneg (topGap S * Real.sqrt (limitingWeight S w) -
    8 * (tiltNorm S R / topGap S * ‖w‖))
  have hq' : (topGap S * Real.sqrt (limitingWeight S w)) ^ 2 ≤
      ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 := by
    rw [mul_pow, hs]
    exact hq
  nlinarith only [hsq, hq', hid]

theorem abs_anisotropy_le_quarter_residual_add_refinedCost (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (hR : R.adjoint = R) (w : R3) (hg : 0 < topGap S) :
    |remainderAnisotropy R (topVector S) w| ≤
      ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 / 4 + refinedCost S R w := by
  have hA := abs_anisotropy_le_tilt_cost S R hR w
  have hT := tilt_cost_le_eighth_residual_add S R w hg
  have hQ := topGap_sq_mul_limitingWeight_le_residual S w
  have hM := mul_le_mul_of_nonneg_right (le_max_left (2 * ‖R‖ - topGap S ^ 2 / 8) 0)
    (limitingWeight_nonneg S w)
  unfold refinedCost
  linarith only [hA, hT, hQ, hM]

theorem abs_anisotropy_le_quarter_residual_add_excess (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (hR : R.adjoint = R) (w : R3) :
    |remainderAnisotropy R (topVector S) w| ≤
      ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 / 4 + excess S R w := by
  have h := (SpectralCommutatorLimit.abs_remainderAnisotropy_le_limitingEnvelope S R w).trans
    (SpectralSourceExcess.envelope_le_quarter_residual_add_excess S R w)
  unfold excess
  split_ifs with hg
  · rw [add_min]
    exact le_min h (abs_anisotropy_le_quarter_residual_add_refinedCost S R hR w hg)
  · exact h

theorem excess_eq_coarse_of_topGap_zero (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (w : R3) (hg : topGap S = 0) : excess S R w = 2 * ‖R‖ * ‖w‖ ^ 2 := by
  simp only [excess, hg, lt_self_iff_false, if_false,
    SpectralSourceExcess.excess_eq_coarse_of_topGap_zero S R w hg]

theorem excess_aligned (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (c : ℝ)
    (hg : 0 < topGap S) : excess S R (c • topVector S) = 0 :=
  le_antisymm (by simpa only [SpectralSourceExcess.excess_aligned S R c hg] using
    excess_le_previous S R (c • topVector S)) (excess_nonneg _ _ _)

/-- Preserving the expanding line suffices; the source may still rotate
the transverse eigenspaces and have a nonzero strain commutator. -/
theorem excess_eq_zero_of_tiltNorm_eq_zero (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (w : R3) (hg : 0 < topGap S) (ht : tiltNorm S R = 0) (hR : 16 * ‖R‖ ≤ topGap S ^ 2) :
    excess S R w = 0 := by
  have hm : 2 * ‖R‖ - topGap S ^ 2 / 8 ≤ 0 := by linarith
  simp only [excess, if_pos hg, refinedCost, max_eq_right hm, zero_mul, ht,
    zero_div, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero,
    min_eq_right (SpectralSourceExcess.excess_nonneg S R w)]

theorem measurable_excess {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : X → SymmetricStrain) (R : X → R3 →L[ℝ] R3) (w : X → R3)
    (hS : Continuous S) (hR : Continuous R) (hw : Continuous w) :
    Measurable (fun x ↦ excess (S x) (R x) (w x)) := by
  let G : Set X := {x | 0 < topGap (S x)}
  have hG : MeasurableSet G := measurableSet_lt measurable_const (continuous_topGap.comp hS).measurable
  have hE := SpectralSourceExcess.measurable_excess S R w hS hR hw
  apply measurable_of_restrict_of_restrict_compl hG
  · have hP := continuous_topEigenlineProjector_restrict_of_topGap_pos S hS G (fun _ hx ↦ hx)
    have hT : Continuous (fun x : G ↦ tiltNorm (S x.1) (R x.1)) :=
      (((continuous_const.sub hP).mul (hR.comp continuous_subtype_val)).mul hP).norm
    have hgap : Measurable (fun x : G ↦ topGap (S x.1)) :=
      ((continuous_topGap.comp hS).comp continuous_subtype_val).measurable
    have hW : Measurable (fun x : G ↦ limitingWeight (S x.1) (w x.1)) :=
      (measurable_limitingWeight S w hS hw).comp measurable_subtype_coe
    have hF : Measurable (fun x : G ↦ refinedCost (S x.1) (R x.1) (w x.1)) :=
      ((((measurable_const.mul (hR.norm.measurable.comp measurable_subtype_coe)).sub
        ((hgap.pow_const 2).div_const 8)).max measurable_const).mul hW).add
        ((measurable_const.mul ((hT.measurable.div hgap).pow_const 2)).mul
          ((hw.norm.pow 2).measurable.comp measurable_subtype_coe))
    have h := (hE.comp measurable_subtype_coe).min hF
    change Measurable (fun x : G ↦ excess (S x.1) (R x.1) (w x.1))
    simpa only [Function.comp_apply, excess, show ∀ x : G, 0 < topGap (S x.1) from fun x ↦ x.2,
      if_true] using h
  · have h : Measurable (fun x : ↥(Gᶜ) ↦ SpectralSourceExcess.excess (S x.1) (R x.1) (w x.1)) :=
      hE.comp measurable_subtype_coe
    change Measurable (fun x : ↥(Gᶜ) ↦ excess (S x.1) (R x.1) (w x.1))
    simpa only [excess, show ∀ x : ↥(Gᶜ), ¬0 < topGap (S x.1) from fun x ↦ x.2,
      if_false] using h

end Mettapedia.FluidDynamics.NavierStokes.SpectralTiltExcess
