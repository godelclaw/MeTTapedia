import Mettapedia.Analysis.SmoothAmplitudePairingEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPairedDiffusion

/-!
# Actual common-translation diffusion with smooth amplitude retention

The exact second derivative includes the weight curvature and both mixed
first variations. All endpoint fields and spatial derivatives are the full
Fourier vorticity objects. Periodicity removes the complete second derivative,
not any selected term. There is no amplitude interface or kernel derivative.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSmoothPairedDiffusion

open MeasureTheory
open Mettapedia.Analysis SmoothAmplitudePairing
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeHaarTransportRate
open PancakeFourierTranslationCurve PancakeInfiniteFourierDerivative
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalSpatialVorticityJets
open PancakeDyadicDirectionEvolution

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def firstRate (n : ℕ) (L : ℝ) (H : Op) (u : FourierVelocity) (h : T3) (j : Fin 3) (x : T3) : ℝ :=
  retainedEndpointRate (n + 1) L H (fullVorticity u x) (fullVorticity u (x - h))
    (fullCurlGradient u j x) (fullCurlGradient u j (x - h))

def secondRate (n : ℕ) (L : ℝ) (H : Op) (u : FourierVelocity) (h : T3) (j : Fin 3) (x : T3) : ℝ :=
  retainedEndpointRate (n + 1) L H (fullVorticity u x) (fullVorticity u (x - h))
      (fullCurlSecond u j x) (fullCurlSecond u j (x - h)) +
    retainedPairCurvature n L H (fullVorticity u x) (fullVorticity u (x - h))
      (fullCurlGradient u j x) (fullCurlGradient u j (x - h))

theorem hasDerivAt_retainedDensity_shift (n : ℕ) (L : ℝ) (hL : 0 < L) (H : Op)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (h : T3) (j : Fin 3) (x : T3) (t : ℝ) :
    HasDerivAt (fun τ ↦ retainedStretch (2 * (n + 2)) L H
      (fullVorticity u (x + coordinateShift j τ))
      (fullVorticity u ((x + coordinateShift j τ) - h)))
      (firstRate n L H u h j (x + coordinateShift j t)) t := by
  have hs (τ : ℝ) : (x - h) + coordinateShift j τ = (x + coordinateShift j τ) - h := by abel
  simpa only [hs, firstRate, show n + 1 + 1 = n + 2 by omega] using
    hasDerivAt_retainedStretch_constKernel (n + 1) L hL H
      (hasDerivAt_fullVorticity_shift u hu j x t)
      (hasDerivAt_fullVorticity_shift u hu j (x - h) t)

theorem continuous_firstRate (n : ℕ) (L : ℝ) (hL : 0 < L) (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) :
    Continuous (firstRate n L H u h j) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hg := LocalSquaredGapGradient.continuous_fullCurlGradient u j
  exact continuous_retainedEndpointRate (n + 1) L hL continuous_const hw
    (hw.comp (continuous_id.sub continuous_const)) hg (hg.comp (continuous_id.sub continuous_const))

theorem continuous_secondRate (n : ℕ) (L : ℝ) (hL : 0 < L) (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) :
    Continuous (secondRate n L H u h j) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hg := LocalSquaredGapGradient.continuous_fullCurlGradient u j
  have hs := LocalPairedDiffusion.continuous_fullCurlSecond u j
  exact (continuous_retainedEndpointRate (n + 1) L hL continuous_const hw
    (hw.comp (continuous_id.sub continuous_const)) hs (hs.comp (continuous_id.sub continuous_const))).add
      (continuous_retainedPairCurvature n L hL continuous_const hw
        (hw.comp (continuous_id.sub continuous_const)) hg (hg.comp (continuous_id.sub continuous_const)))

theorem hasDerivAt_firstRate_shift (n : ℕ) (L : ℝ) (hL : 0 < L) (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) (x : T3) (t : ℝ) :
    HasDerivAt (fun τ ↦ firstRate n L H u h j (x + coordinateShift j τ))
      (secondRate n L H u h j (x + coordinateShift j t)) t := by
  have hs (τ : ℝ) : (x - h) + coordinateShift j τ = (x + coordinateShift j τ) - h := by abel
  have hd := hasDerivAt_retainedEndpointRate n L hL H
    (hasDerivAt_fullVorticity_shift u hu j x t)
    (hasDerivAt_fullVorticity_shift u hu j (x - h) t)
    (hasDerivAt_fullCurlGradient_shift u hu j x t)
    (hasDerivAt_fullCurlGradient_shift u hu j (x - h) t)
  simpa only [hs, firstRate, secondRate] using hd

theorem integral_secondRate_eq_zero (n : ℕ) (L : ℝ) (hL : 0 < L) (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) :
    (∫ x : T3, secondRate n L H u h j x) = 0 :=
  UnitTorusContinuousRate.integral_rate_eq_zero (firstRate n L H u h j) (secondRate n L H u h j)
    (coordinateShift j) (continuous_firstRate n L hL H u hu h j)
    (continuous_secondRate n L hL H u hu h j) (continuous_coordinateShift j) (coordinateShift_zero j)
    (hasDerivAt_firstRate_shift n L hL H u hu h j)

def curvature (n : ℕ) (L : ℝ) (H : Op) (u : FourierVelocity) (h x : T3) : ℝ :=
  ∑ j : Fin 3, retainedPairCurvature n L H (fullVorticity u x) (fullVorticity u (x - h))
    (fullCurlGradient u j x) (fullCurlGradient u j (x - h))

def diffusion (n : ℕ) (L : ℝ) (H : Op) (u : FourierVelocity) (h x : T3) : ℝ :=
  retainedEndpointRate (n + 1) L H (fullVorticity u x) (fullVorticity u (x - h))
    (fullVorticityLaplacian u x) (fullVorticityLaplacian u (x - h))

theorem sum_secondRate_eq (n : ℕ) (L : ℝ) (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h x : T3) :
    (∑ j : Fin 3, secondRate n L H u h j x) = diffusion n L H u h x + curvature n L H u h x := by
  simp only [secondRate, Finset.sum_add_distrib, diffusion, curvature,
    ← retainedEndpointRate_sum, sum_fullCurlSecond u hu]

/-- The complete smooth-retention curvature, with no sign or budget assumption. -/
theorem integral_diffusion_eq_neg_curvature (n : ℕ) (L : ℝ) (hL : 0 < L) (H : Op)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (h : T3) :
    (∫ x : T3, diffusion n L H u h x) = -(∫ x : T3, curvature n L H u h x) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hl := LocalPairedDiffusion.continuous_fullVorticityLaplacian u hu
  have hd : Continuous (diffusion n L H u h) :=
    continuous_retainedEndpointRate (n + 1) L hL continuous_const hw
      (hw.comp (continuous_id.sub continuous_const)) hl (hl.comp (continuous_id.sub continuous_const))
  have hc : Continuous (curvature n L H u h) := continuous_finsetSum _ (fun j _ ↦
    continuous_retainedPairCurvature n L hL continuous_const hw (hw.comp (continuous_id.sub continuous_const))
      (LocalSquaredGapGradient.continuous_fullCurlGradient u j)
      ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp (continuous_id.sub continuous_const)))
  have hzero : (∫ x : T3, ∑ j : Fin 3, secondRate n L H u h j x) = 0 := by
    rw [integral_finsetSum Finset.univ (fun j _ ↦
      (continuous_secondRate n L hL H u hu h j).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    simp only [integral_secondRate_eq_zero n L hL H u hu h, Finset.sum_const_zero]
  simp only [sum_secondRate_eq n L H u hu h] at hzero
  rw [integral_add (hd.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))] at hzero
  linarith

end Mettapedia.FluidDynamics.NavierStokes.LocalSmoothPairedDiffusion
