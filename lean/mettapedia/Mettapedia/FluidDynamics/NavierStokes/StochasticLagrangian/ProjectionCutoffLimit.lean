import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalProjectionStrainBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteBandProjectionAbsorption
import Mathlib.Topology.Algebra.Order.Field

/-!
# Oversized-cutoff limit of the signed strain remainder

For a fixed regular field, the normalized signed strain remainder tends
to its original vortex stretching, not to zero. The error estimate is
uniform in positive regularization. Thus a large normalization alone
cannot establish depletion of the complete nonlinear work.

This is a consistency test of an estimate, not a blowup result or a
refutation of a time-dependent geometric mechanism.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ProjectionCutoffLimit

open scoped Topology
open Filter
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalWeightedCurlCancellation LocalVorticityEighthMoment LocalProjectionStrainRate
open LocalProjectionStrainBound FiniteBandProjectionAbsorption
open LocalWeightedProjectionEvolution

def strainRemainder (δ κ : ℝ) (u : FourierVelocity) : ℝ :=
  -(weightedStrainSpectralDefect κ u + 3 * strainMaterialWork δ u) / κ

def fixedFieldEnvelope (u : FourierVelocity) : ℝ :=
  6 * |longitudinalHelicityIntegral u| + 3 * strainWorkEnvelope u

theorem fixedFieldEnvelope_nonneg (u : FourierVelocity) : 0 ≤ fixedFieldEnvelope u := by
  have h := strainWorkEnvelope_nonneg u
  unfold fixedFieldEnvelope
  positivity

theorem strainRemainder_sub_stretching (δ κ : ℝ) (hκ : κ ≠ 0) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0) :
    strainRemainder δ κ u - stretching u =
      (6 * longitudinalHelicityIntegral u - 3 * strainMaterialWork δ u) / κ := by
  have h := stretching_spectral_identity u hu hd κ
  unfold strainRemainder
  field_simp
  linarith only [h]

/-- Uniform over every positive regularization; the fixed-field constant
is not claimed to be bounded by the unforced kinetic-energy budget. -/
theorem abs_strainRemainder_sub_stretching_le (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0) :
    |strainRemainder δ κ u - stretching u| ≤ fixedFieldEnvelope u / κ := by
  rw [strainRemainder_sub_stretching δ κ hκ.ne' u hu hd, abs_div, abs_of_pos hκ]
  apply div_le_div_of_nonneg_right _ hκ.le
  have h := abs_strainMaterialWork_le δ hδ u
    (summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu)
  calc
    _ ≤ |6 * longitudinalHelicityIntegral u| + |3 * strainMaterialWork δ u| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (6 * longitudinalHelicityIntegral u) (-(3 * strainMaterialWork δ u))
    _ ≤ fixedFieldEnvelope u := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), fixedFieldEnvelope]
      linarith only [h]

theorem tendsto_normalization : Tendsto normalization atTop atTop := by
  have h : Tendsto (fun R : ℝ ↦ 48 * (8 * Real.pi * R) ^ 2) atTop atTop :=
    ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
      (tendsto_id.const_mul_atTop (by positivity : 0 < 8 * Real.pi))).const_mul_atTop (by norm_num)
  exact tendsto_atTop_mono coercivity_scale_le h

theorem tendsto_strainRemainder (ν : ℝ) (hν : 0 < ν) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0) :
    Tendsto (fun R : ℝ ↦ strainRemainder (regularization ν R) (normalization R) u)
      atTop (𝓝 (stretching u)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun R ↦ norm_nonneg _) (fun R ↦ ?_)
    (tendsto_normalization.const_div_atTop (fixedFieldEnvelope u))
  simpa only [Real.norm_eq_abs] using
    abs_strainRemainder_sub_stretching_le _ _ (regularization_pos ν R hν) (normalization_pos R) u hu hd

/-- The same cutoff family cannot tend to zero on a field with nonzero
stretching. The nonzero-stretching hypothesis is explicit. -/
theorem not_tendsto_strainRemainder_zero (ν : ℝ) (hν : 0 < ν) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hstretch : stretching u ≠ 0) :
    ¬ Tendsto (fun R : ℝ ↦ strainRemainder (regularization ν R) (normalization R) u) atTop (𝓝 0) := by
  intro hzero
  exact hstretch (tendsto_nhds_unique (tendsto_strainRemainder ν hν u hu hd) hzero)

/-- A positive stretching snapshot eventually retains at least half its
stretching in the signed remainder, despite arbitrarily large cutoff. -/
theorem eventually_half_stretching_le (ν : ℝ) (hν : 0 < ν) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hstretch : 0 < stretching u) :
    ∀ᶠ R : ℝ in atTop, stretching u / 2 ≤ strainRemainder (regularization ν R) (normalization R) u := by
  have h := (tendsto_strainRemainder ν hν u hu hd).eventually
    (Ioi_mem_nhds (show stretching u / 2 < stretching u by linarith))
  filter_upwards [h] with R hR
  exact hR.le

theorem abs_correctedEnergy_sub_le (ν : ℝ) (hν : 0 < ν) (R : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    |correctedEnergy ν R u - meanEnergy u / 8| ≤ 6 * weightedPalinstrophy u / normalization R := by
  have hδ := regularization_pos ν R hν
  have hκ := normalization_pos R
  have hK : 0 ≤ weightedProjectionEnergy (regularization ν R) u :=
    MeasureTheory.integral_nonneg (weightedProjectionDensity_nonneg _ hδ.le u)
  have he : correctedEnergy ν R u - meanEnergy u / 8 =
      -(3 / normalization R * weightedProjectionEnergy (regularization ν R) u) := by
    unfold correctedEnergy
    ring
  rw [he, abs_neg, abs_of_nonneg (mul_nonneg (by positivity) hK)]
  have h := mul_le_mul_of_nonneg_left (weightedProjectionEnergy_le _ hδ u hu)
    (show 0 ≤ 3 / normalization R by positivity)
  calc
    _ ≤ (3 / normalization R) * (2 * weightedPalinstrophy u) := h
    _ = _ := by ring

/-- On a fixed field the correction itself vanishes in the oversized-cutoff
limit, consistently with the return of ordinary stretching. -/
theorem tendsto_correctedEnergy (ν : ℝ) (hν : 0 < ν) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    Tendsto (fun R : ℝ ↦ correctedEnergy ν R u) atTop (𝓝 (meanEnergy u / 8)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun R ↦ norm_nonneg _) (fun R ↦ ?_)
    (tendsto_normalization.const_div_atTop (6 * weightedPalinstrophy u))
  simpa only [Real.norm_eq_abs] using abs_correctedEnergy_sub_le ν hν R u hu

end Mettapedia.FluidDynamics.NavierStokes.ProjectionCutoffLimit
