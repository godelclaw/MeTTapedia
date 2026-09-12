import Mettapedia.Analysis.PeriodicRieszOperator
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityHighAmplitudeSource

/-!
# A cutoff-uniform increment budget for the regularized stretching kernels

The constructed even Riesz kernel family pays cubic radial increments with
the actual weighted palinstrophy. Unlike the sharp finite-frequency bound,
the constant and the positive dissipation threshold are independent of the
cutoff. Identifying the full signed source with the limit of this new
regularization and controlling its high-amplitude part are separate steps.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedIncrement

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments LocalLowDiffusionBudget PeriodicWeightedIncrement
open GaussianRootWeightedIncrement Mettapedia.Analysis.RadialPower
open Mettapedia.Analysis.SignedCrossKernel

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "K" => Mettapedia.Analysis.PeriodicRieszOperator.kernel (d := 3)
local notation "C" => Mettapedia.Analysis.PeriodicRieszOperator.secondMomentBound 3
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def incrementIntegral (N : ℕ) (u : FourierVelocity) : ℝ :=
  ∫ h : T3, ‖K N h‖ * ∫ x : T3,
    ‖radialPower 3 (fullVorticity u x) - radialPower 3 (fullVorticity u (x - h))‖ ^ 2

theorem increment_at_displacement_le (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (h : T3) :
    (∫ x : T3, ‖radialPower 3 (fullVorticity u x) - radialPower 3 (fullVorticity u (x - h))‖ ^ 2) ≤
      48 * ‖h‖ ^ 2 * LocalVorticityEighthMoment.weightedPalinstrophy u := by
  have hu1 := summable_fourierMoment_of_le u (by norm_num : 1 ≤ 3) hu
  have hu2 := summable_fourierMoment_of_le u (by norm_num : 2 ≤ 3) hu
  have hb := integral_radialPower_three_sub_le (fullVorticity u) (continuous_fullVorticity u hu1)
    (LocalAlignmentTransport.locallyLipschitz_fullVorticity u hu2) h
  simpa only [weightedGradientDensity_fullVorticity u hu,
    LocalVorticityEighthMoment.weightedPalinstrophy] using hb

theorem integrable_increment (N : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    Integrable (fun h : T3 ↦ ‖K N h‖ * ∫ x : T3,
      ‖radialPower 3 (fullVorticity u x) - radialPower 3 (fullVorticity u (x - h))‖ ^ 2) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by norm_num : 1 ≤ 3) hu)
  have hg : Continuous (fun x : T3 ↦ radialPower 3 (fullVorticity u x)) :=
    (continuous_radialPower 3).comp hw
  have hc : Continuous (fun p : T3 × T3 ↦
      ‖radialPower 3 (fullVorticity u p.2) - radialPower 3 (fullVorticity u (p.2 - p.1))‖ ^ 2) :=
    ((hg.comp continuous_snd).sub (hg.comp (continuous_snd.sub continuous_fst))).norm.pow 2
  have hm : AEStronglyMeasurable (fun h : T3 ↦ ‖K N h‖ * ∫ x : T3,
      ‖radialPower 3 (fullVorticity u x) - radialPower 3 (fullVorticity u (x - h))‖ ^ 2)
      (volume : Measure T3) :=
    (Mettapedia.Analysis.PeriodicRieszOperator.measurable_kernel (d := 3) N).norm.aestronglyMeasurable.mul
      (hc.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure T3))).aestronglyMeasurable
  apply ((Mettapedia.Analysis.PeriodicRieszOperator.integrable_secondMoment (d := 3) N).const_mul
    (48 * LocalVorticityEighthMoment.weightedPalinstrophy u)).mono' hm
  filter_upwards [] with h
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (integral_nonneg (fun _ ↦ sq_nonneg _)))]
  have hb := mul_le_mul_of_nonneg_left (increment_at_displacement_le u hu h) (norm_nonneg (K N h))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hb

theorem incrementIntegral_le (N : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    incrementIntegral N u ≤ 48 * C * LocalVorticityEighthMoment.weightedPalinstrophy u := by
  have hi := (Mettapedia.Analysis.PeriodicRieszOperator.integrable_secondMoment (d := 3) N).const_mul
    (48 * LocalVorticityEighthMoment.weightedPalinstrophy u)
  have hb := integral_mono (integrable_increment N u hu) hi (fun h ↦ by
    have h := mul_le_mul_of_nonneg_left (increment_at_displacement_le u hu h) (norm_nonneg (K N h))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h)
  rw [integral_const_mul] at hb
  have hG := LocalVorticityEighthMoment.weightedPalinstrophy_nonneg u
  have hk := mul_le_mul_of_nonneg_left (Mettapedia.Analysis.PeriodicRieszOperator.secondMoment_le (d := 3) N)
    (show 0 ≤ 48 * LocalVorticityEighthMoment.weightedPalinstrophy u by positivity)
  exact hb.trans (hk.trans_eq (by ring))

/-- One threshold works for every regularization cutoff. -/
def dissipationThreshold (nu : ℝ) : ℝ := nu / (192 * (C + 1))

theorem dissipationThreshold_pos (nu : ℝ) (hnu : 0 < nu) : 0 < dissipationThreshold nu := by
  have hC := Mettapedia.Analysis.PeriodicRieszOperator.secondMomentBound_nonneg 3
  unfold dissipationThreshold
  positivity

theorem dissipationThreshold_pays (nu : ℝ) (hnu : 0 ≤ nu) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    2 * dissipationThreshold nu * incrementIntegral N u ≤
      (nu / 2) * LocalVorticityEighthMoment.weightedPalinstrophy u := by
  have hC := Mettapedia.Analysis.PeriodicRieszOperator.secondMomentBound_nonneg 3
  have hL : 0 ≤ dissipationThreshold nu := by unfold dissipationThreshold; positivity
  have hp : 96 * dissipationThreshold nu * C ≤ nu / 2 := by
    unfold dissipationThreshold
    rw [← mul_div_assoc, div_mul_eq_mul_div, div_le_iff₀ (show 0 < 192 * (C + 1) by positivity)]
    nlinarith
  have hb := mul_le_mul_of_nonneg_left (incrementIntegral_le N u hu) (show 0 ≤ 2 * dissipationThreshold nu by positivity)
  have hg := mul_le_mul_of_nonneg_right hp (LocalVorticityEighthMoment.weightedPalinstrophy_nonneg u)
  nlinarith only [hb, hg]

end Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedIncrement
