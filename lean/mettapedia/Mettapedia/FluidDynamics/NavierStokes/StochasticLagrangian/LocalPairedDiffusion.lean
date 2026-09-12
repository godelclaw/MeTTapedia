import Mettapedia.Analysis.SignedCrossKernelCurvature
import Mettapedia.Analysis.UnitTorusContinuousRate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityEighthSpatialBalance

/-!
# Common-translation diffusion of the actual paired vorticity source

Fix the endpoint separation before differentiating. The kernel is then a
constant operator, while both full vorticity fields are translated together.
Periodic integration cancels the second translation derivative and leaves
the explicit signed curvature. There is no kernel derivative or receiver
truncation. This is the smooth paired source, before an amplitude cutoff.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalPairedDiffusion

open MeasureTheory
open Mettapedia.Analysis SignedCrossKernel
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

def firstRate (n : ℕ) (H : Op) (u : FourierVelocity) (h : T3) (j : Fin 3) (x : T3) : ℝ :=
  pairedEndpointRate (n + 1) H (fullVorticity u x) (fullVorticity u (x - h))
    (fullCurlGradient u j x) (fullCurlGradient u j (x - h))

def secondRate (n : ℕ) (H : Op) (u : FourierVelocity) (h : T3) (j : Fin 3) (x : T3) : ℝ :=
  pairedEndpointRate (n + 1) H (fullVorticity u x) (fullVorticity u (x - h))
      (fullCurlSecond u j x) (fullCurlSecond u j (x - h)) +
    pairedCurvature n H (fullVorticity u x) (fullVorticity u (x - h))
      (fullCurlGradient u j x) (fullCurlGradient u j (x - h))

theorem continuous_fullCurlSecond (u : FourierVelocity) (j : Fin 3) :
    Continuous (fullCurlSecond u j) :=
  complexRealPartEuclideanCLM.continuous.comp (fullFourierField id _).continuous

theorem continuous_fullVorticityLaplacian (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) : Continuous (fullVorticityLaplacian u) := by
  have h := continuous_finsetSum (Finset.univ : Finset (Fin 3))
    (fun j _ ↦ continuous_fullCurlSecond u j)
  simpa only [sum_fullCurlSecond u hu] using h

theorem continuous_firstRate (n : ℕ) (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) :
    Continuous (firstRate n H u h j) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hg := LocalSquaredGapGradient.continuous_fullCurlGradient u j
  exact continuous_pairedEndpointRate (n + 1) continuous_const hw
    (hw.comp (continuous_id.sub continuous_const)) hg (hg.comp (continuous_id.sub continuous_const))

theorem continuous_secondRate (n : ℕ) (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) :
    Continuous (secondRate n H u h j) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hg := LocalSquaredGapGradient.continuous_fullCurlGradient u j
  have hs := continuous_fullCurlSecond u j
  exact (continuous_pairedEndpointRate (n + 1) continuous_const hw
    (hw.comp (continuous_id.sub continuous_const)) hs (hs.comp (continuous_id.sub continuous_const))).add
      (continuous_pairedCurvature n continuous_const hw
        (hw.comp (continuous_id.sub continuous_const)) hg (hg.comp (continuous_id.sub continuous_const)))

theorem hasDerivAt_firstRate_shift (n : ℕ) (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) (x : T3) (t : ℝ) :
    HasDerivAt (fun τ ↦ firstRate n H u h j (x + coordinateShift j τ))
      (secondRate n H u h j (x + coordinateShift j t)) t := by
  have hs (τ : ℝ) : (x - h) + coordinateShift j τ = (x + coordinateShift j τ) - h := by abel
  have hd := hasDerivAt_pairedEndpointRate n H
    (hasDerivAt_fullVorticity_shift u hu j x t)
    (hasDerivAt_fullVorticity_shift u hu j (x - h) t)
    (hasDerivAt_fullCurlGradient_shift u hu j x t)
    (hasDerivAt_fullCurlGradient_shift u hu j (x - h) t)
  simpa only [hs, firstRate, secondRate] using hd

theorem integral_secondRate_eq_zero (n : ℕ) (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) :
    (∫ x : T3, secondRate n H u h j x) = 0 :=
  UnitTorusContinuousRate.integral_rate_eq_zero (firstRate n H u h j) (secondRate n H u h j)
    (coordinateShift j) (continuous_firstRate n H u hu h j) (continuous_secondRate n H u hu h j)
    (continuous_coordinateShift j) (coordinateShift_zero j)
    (hasDerivAt_firstRate_shift n H u hu h j)

def curvature (n : ℕ) (H : Op) (u : FourierVelocity) (h x : T3) : ℝ :=
  ∑ j : Fin 3, pairedCurvature n H (fullVorticity u x) (fullVorticity u (x - h))
    (fullCurlGradient u j x) (fullCurlGradient u j (x - h))

def diffusion (n : ℕ) (H : Op) (u : FourierVelocity) (h x : T3) : ℝ :=
  pairedEndpointRate (n + 1) H (fullVorticity u x) (fullVorticity u (x - h))
    (fullVorticityLaplacian u x) (fullVorticityLaplacian u (x - h))

theorem sum_secondRate_eq (n : ℕ) (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h x : T3) :
    (∑ j : Fin 3, secondRate n H u h j x) = diffusion n H u h x + curvature n H u h x := by
  simp only [secondRate, Finset.sum_add_distrib, diffusion, curvature,
    ← pairedEndpointRate_sum, sum_fullCurlSecond u hu]

/-- Exact diffusion identity with signed curvature and no kernel derivative. -/
theorem integral_diffusion_eq_neg_curvature (n : ℕ) (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) :
    (∫ x : T3, diffusion n H u h x) = -(∫ x : T3, curvature n H u h x) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hl := continuous_fullVorticityLaplacian u hu
  have hd : Continuous (diffusion n H u h) :=
    continuous_pairedEndpointRate (n + 1) continuous_const hw
      (hw.comp (continuous_id.sub continuous_const)) hl (hl.comp (continuous_id.sub continuous_const))
  have hc : Continuous (curvature n H u h) := continuous_finsetSum _ (fun j _ ↦
    continuous_pairedCurvature n continuous_const hw (hw.comp (continuous_id.sub continuous_const))
      (LocalSquaredGapGradient.continuous_fullCurlGradient u j)
      ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp (continuous_id.sub continuous_const)))
  have hzero : (∫ x : T3, ∑ j : Fin 3, secondRate n H u h j x) = 0 := by
    rw [integral_finsetSum Finset.univ (fun j _ ↦
      (continuous_secondRate n H u hu h j).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    simp only [integral_secondRate_eq_zero n H u hu h, Finset.sum_const_zero]
  simp only [sum_secondRate_eq n H u hu h] at hzero
  rw [integral_add (hd.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))] at hzero
  linarith

end Mettapedia.FluidDynamics.NavierStokes.LocalPairedDiffusion
