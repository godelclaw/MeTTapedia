import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRadialSourceBound
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Dissipation pays the bounded-amplitude source while the remainder stays signed

At each fixed finite strain cutoff, a continuous symmetric amplitude weight
separates off the source whose smaller endpoint norm is below a prescribed
positive threshold. The difference from the signed high-amplitude source
is bounded by the actual weighted palinstrophy and the kernel's second
moment. The remainder vanishes unless both vorticity endpoints exceed the
threshold. No cutoff-uniform or dynamical bound on that remainder is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityHighAmplitudeSource

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeBlockReality PancakePeriodicComplexStretch PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget VorticityStretchingKernel VorticityWeightedStretching
open PeriodicWeightedIncrement GaussianRootWeightedIncrement
open Mettapedia.Analysis.SignedCrossKernel Mettapedia.Analysis.RadialPower

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

def kernelSecondMoment (modes : Finset Wavevector) : ℝ :=
  ∫ h : T3, ‖h‖ ^ 2 * ‖kernel modes h‖

def bareRadialIntegral (n : ℕ) (modes : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ∫ y : T3, ‖kernel modes (x - y)‖ *
    ‖radialPower n (fullVorticity u x) - radialPower n (fullVorticity u y)‖ ^ 2

def highAmplitudeSource (n : ℕ) (L : ℝ) (modes : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3,
    highAmplitudeStretch n L (kernel modes (x - y)) (fullVorticity u x) (fullVorticity u y)

theorem kernelSecondMoment_nonneg (modes : Finset Wavevector) : 0 ≤ kernelSecondMoment modes :=
  integral_nonneg (fun _ ↦ by positivity)

/-- A cutoff-dependent threshold that reserves half the weighted dissipation. -/
def dissipationThreshold (nu : ℝ) (modes : Finset Wavevector) : ℝ :=
  nu / (192 * (kernelSecondMoment modes + 1))

theorem dissipationThreshold_pos (nu : ℝ) (hnu : 0 < nu) (modes : Finset Wavevector) :
    0 < dissipationThreshold nu modes := by
  have hm := kernelSecondMoment_nonneg modes
  unfold dissipationThreshold
  positivity

theorem dissipationThreshold_pays (nu : ℝ) (hnu : 0 ≤ nu) (modes : Finset Wavevector) :
    96 * dissipationThreshold nu modes * kernelSecondMoment modes ≤ nu / 2 := by
  have hm := kernelSecondMoment_nonneg modes
  have hd : 0 < 192 * (kernelSecondMoment modes + 1) := by positivity
  unfold dissipationThreshold
  rw [← mul_div_assoc, div_mul_eq_mul_div, div_le_iff₀ hd]
  nlinarith

theorem bareRadialIntegral_three_le (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    bareRadialIntegral 3 modes u ≤
      48 * kernelSecondMoment modes * LocalVorticityEighthMoment.weightedPalinstrophy u := by
  have hu1 := summable_fourierMoment_of_le u (by norm_num : 1 ≤ 3) hu
  have hu2 := summable_fourierMoment_of_le u (by norm_num : 2 ≤ 3) hu
  have hw := continuous_fullVorticity u hu1
  let g : T3 → R3 := fun x ↦ radialPower 3 (fullVorticity u x)
  have hg : Continuous g := (continuous_radialPower 3).comp hw
  have hc : Continuous (fun p : T3 × T3 ↦ ‖kernel modes p.1‖ * ‖g p.2 - g (p.2 - p.1)‖ ^ 2) :=
    ((continuous_kernel modes).comp continuous_fst).norm.mul
      (((hg.comp continuous_snd).sub (hg.comp (continuous_snd.sub continuous_fst))).norm.pow 2)
  have hi := hc.integrable_of_hasCompactSupport (μ := (volume : Measure T3).prod volume)
    (HasCompactSupport.of_compactSpace _)
  have he : bareRadialIntegral 3 modes u =
      ∫ x : T3, ∫ h : T3, ‖kernel modes h‖ * ‖g x - g (x - h)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with x
    have ht := integral_sub_left_eq_self
      (fun y : T3 ↦ ‖kernel modes (x - y)‖ * ‖g x - g y‖ ^ 2)
      (volume : Measure T3) x
    simpa only [sub_sub_cancel] using ht.symm
  rw [he, ← integral_integral_swap hi]
  have hm : Integrable (fun h : T3 ↦ ‖h‖ ^ 2 * ‖kernel modes h‖) :=
    ((continuous_norm.pow 2).mul (continuous_kernel modes).norm).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp (h : T3) : (∫ x : T3, ‖kernel modes h‖ * ‖g x - g (x - h)‖ ^ 2) ≤
      (48 * (‖h‖ ^ 2 * ‖kernel modes h‖)) * LocalVorticityEighthMoment.weightedPalinstrophy u := by
    rw [integral_const_mul]
    have hs := integral_radialPower_three_sub_le (fullVorticity u) hw
      (LocalAlignmentTransport.locallyLipschitz_fullVorticity u hu2) h
    simp only [weightedGradientDensity_fullVorticity u hu] at hs
    have hb := mul_le_mul_of_nonneg_left hs (norm_nonneg (kernel modes h))
    exact hb.trans_eq (by change _ = _ * (∫ x : T3, weightedPalinstrophyDensity u x); ring)
  have hb := integral_mono hi.integral_prod_left ((hm.const_mul 48).mul_const _) hp
  simpa only [integral_mul_const, integral_const_mul, kernelSecondMoment] using hb

/-- The high-amplitude term is signed; only its complement is charged to dissipation. -/
theorem abs_finiteStretching_sub_highAmplitudeSource_le (L : ℝ) (hL : 0 < L)
    (modes : Finset Wavevector) (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    |finiteStretching 6 modes u - highAmplitudeSource 6 L modes u| ≤
      96 * L * kernelSecondMoment modes * LocalVorticityEighthMoment.weightedPalinstrophy u := by
  have hu1 := summable_fourierMoment_of_le u (by norm_num : 1 ≤ 3) hu
  rw [finiteStretching_eq_pair 6 modes u hu1 hr hd, pairedIntegral, highAmplitudeSource,
    ← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h := abs_integral_paired_sub_high_le (volume : Measure T3)
    (fun x y ↦ kernel modes (x - y)) (fullVorticity u)
    ((continuous_kernel modes).comp (continuous_fst.sub continuous_snd))
    (continuous_fullVorticity u hu1) 3 L hL
  change _ ≤ 4 * L * bareRadialIntegral 3 modes u at h
  calc
    _ ≤ (1 / 2 : ℝ) * (4 * L * bareRadialIntegral 3 modes u) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 2 * L * bareRadialIntegral 3 modes u := by ring
    _ ≤ 2 * L * (48 * kernelSecondMoment modes * LocalVorticityEighthMoment.weightedPalinstrophy u) :=
      mul_le_mul_of_nonneg_left (bareRadialIntegral_three_le modes u hu) (by positivity)
    _ = _ := by ring

theorem finiteStretching_le_half_dissipation_add_highAmplitudeSource
    (nu L : ℝ) (hL : 0 < L) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0)
    (hpay : 96 * L * kernelSecondMoment modes ≤ nu / 2) :
    finiteStretching 6 modes u ≤
      (nu / 2) * LocalVorticityEighthMoment.weightedPalinstrophy u + highAmplitudeSource 6 L modes u := by
  have h := (le_abs_self _).trans (abs_finiteStretching_sub_highAmplitudeSource_le L hL modes u hu hr hd)
  have hp := mul_le_mul_of_nonneg_right hpay (LocalVorticityEighthMoment.weightedPalinstrophy_nonneg u)
  linarith only [h, hp]

theorem highAmplitudeStretch_eq_zero_of_endpoint_le (L : ℝ) (hL : 0 < L)
    (modes : Finset Wavevector) (u : FourierVelocity) (x y : T3)
    (h : ‖fullVorticity u x‖ ≤ L ∨ ‖fullVorticity u y‖ ≤ L) :
    highAmplitudeStretch 6 L (kernel modes (x - y)) (fullVorticity u x) (fullVorticity u y) = 0 := by
  apply highAmplitudeStretch_eq_zero_of_min_le _ L hL
  rcases h with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans h

/-- The threshold is constructed from viscosity and the finite kernel, not from a field bound. -/
theorem finiteStretching_le_half_dissipation_add_remainder
    (nu : ℝ) (hnu : 0 < nu) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    finiteStretching 6 modes u ≤
      (nu / 2) * LocalVorticityEighthMoment.weightedPalinstrophy u +
        highAmplitudeSource 6 (dissipationThreshold nu modes) modes u :=
  finiteStretching_le_half_dissipation_add_highAmplitudeSource nu _
    (dissipationThreshold_pos nu hnu modes) modes u hu hr hd
    (dissipationThreshold_pays nu hnu.le modes)

end Mettapedia.FluidDynamics.NavierStokes.VorticityHighAmplitudeSource
