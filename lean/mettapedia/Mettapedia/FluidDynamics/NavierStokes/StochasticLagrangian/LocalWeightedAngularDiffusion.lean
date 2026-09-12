import Mettapedia.Analysis.WeightedCrossProductCurvature
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedAngularEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPairedDiffusion

/-!
# Spatially integrated viscosity of the weighted angular cost

Common translation keeps the separation kernel fixed. Periodicity cancels
the full second derivative and leaves minus the complete endpoint curvature.
This is the actual vorticity Laplacian contribution, not a sign assumption
or an evolution identity for the remaining transport and strain terms.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalWeightedAngularDiffusion

open MeasureTheory
open Mettapedia.Analysis WeightedCrossProduct
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeHaarTransportRate
open PancakeFourierTranslationCurve PancakeInfiniteFourierDerivative
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalSpatialVorticityJets
open PancakeDyadicDirectionEvolution

local notation "T3" => UnitAddTorus (Fin 3)
local notation "H" => PeriodicRieszOperator.kernel (d := 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def firstRate (n : ℕ) (u : FourierVelocity) (h : T3) (j : Fin 3) (x : T3) : ℝ :=
  rate (n + 1) (fullVorticity u x) (fullVorticity u (x - h))
    (fullCurlGradient u j x) (fullCurlGradient u j (x - h))

def secondRate (n : ℕ) (u : FourierVelocity) (h : T3) (j : Fin 3) (x : T3) : ℝ :=
  rate (n + 1) (fullVorticity u x) (fullVorticity u (x - h))
      (fullCurlSecond u j x) (fullCurlSecond u j (x - h)) +
    WeightedCrossProduct.curvature n (fullVorticity u x) (fullVorticity u (x - h))
      (fullCurlGradient u j x) (fullCurlGradient u j (x - h))

theorem continuous_firstRate (n : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) :
    Continuous (firstRate n u h j) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hg := LocalSquaredGapGradient.continuous_fullCurlGradient u j
  exact continuous_rate (n + 1) hw (hw.comp (continuous_id.sub continuous_const))
    hg (hg.comp (continuous_id.sub continuous_const))

theorem continuous_secondRate (n : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) :
    Continuous (secondRate n u h j) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hg := LocalSquaredGapGradient.continuous_fullCurlGradient u j
  have hs := LocalPairedDiffusion.continuous_fullCurlSecond u j
  exact (continuous_rate (n + 1) hw (hw.comp (continuous_id.sub continuous_const))
    hs (hs.comp (continuous_id.sub continuous_const))).add
      (continuous_curvature n hw (hw.comp (continuous_id.sub continuous_const))
        hg (hg.comp (continuous_id.sub continuous_const)))

theorem hasDerivAt_firstRate_shift (n : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) (x : T3) (t : ℝ) :
    HasDerivAt (fun τ ↦ firstRate n u h j (x + coordinateShift j τ))
      (secondRate n u h j (x + coordinateShift j t)) t := by
  have hs (τ : ℝ) : (x - h) + coordinateShift j τ = (x + coordinateShift j τ) - h := by abel
  have hd := hasDerivAt_rate n
    (hasDerivAt_fullVorticity_shift u hu j x t)
    (hasDerivAt_fullVorticity_shift u hu j (x - h) t)
    (hasDerivAt_fullCurlGradient_shift u hu j x t)
    (hasDerivAt_fullCurlGradient_shift u hu j (x - h) t)
  simpa only [hs, firstRate, secondRate] using hd

theorem integral_secondRate_eq_zero (n : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) :
    (∫ x : T3, secondRate n u h j x) = 0 :=
  UnitTorusContinuousRate.integral_rate_eq_zero (firstRate n u h j) (secondRate n u h j)
    (coordinateShift j) (continuous_firstRate n u hu h j) (continuous_secondRate n u hu h j)
    (continuous_coordinateShift j) (coordinateShift_zero j)
    (hasDerivAt_firstRate_shift n u hu h j)

def curvatureDensity (n : ℕ) (u : FourierVelocity) (h x : T3) : ℝ :=
  ∑ j : Fin 3, WeightedCrossProduct.curvature n (fullVorticity u x) (fullVorticity u (x - h))
    (fullCurlGradient u j x) (fullCurlGradient u j (x - h))

def diffusionDensity (n : ℕ) (u : FourierVelocity) (h x : T3) : ℝ :=
  rate (n + 1) (fullVorticity u x) (fullVorticity u (x - h))
    (fullVorticityLaplacian u x) (fullVorticityLaplacian u (x - h))

theorem continuous_diffusionDensity (n : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) : Continuous (diffusionDensity n u).uncurry := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hl := LocalPairedDiffusion.continuous_fullVorticityLaplacian u hu
  exact continuous_rate (n + 1) (hw.comp continuous_snd)
    (hw.comp (continuous_snd.sub continuous_fst)) (hl.comp continuous_snd)
    (hl.comp (continuous_snd.sub continuous_fst))

theorem continuous_curvatureDensity (n : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : Continuous (curvatureDensity n u).uncurry := by
  have hw := continuous_fullVorticity u hu
  exact continuous_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ ↦
    continuous_curvature n (hw.comp continuous_snd) (hw.comp (continuous_snd.sub continuous_fst))
      ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_snd)
      ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp
        (continuous_snd.sub continuous_fst)))

theorem sum_secondRate_eq (n : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h x : T3) :
    (∑ j : Fin 3, secondRate n u h j x) = diffusionDensity n u h x + curvatureDensity n u h x := by
  simp only [secondRate, Finset.sum_add_distrib, diffusionDensity, curvatureDensity,
    ← rate_sum, sum_fullCurlSecond u hu]

theorem integral_diffusion_eq_neg_curvature (n : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) :
    (∫ x : T3, diffusionDensity n u h x) = -(∫ x : T3, curvatureDensity n u h x) := by
  have hd : Continuous (diffusionDensity n u h) :=
    (continuous_diffusionDensity n u hu).comp (f := fun x : T3 ↦ (h, x))
      (continuous_const.prodMk continuous_id)
  have hc : Continuous (curvatureDensity n u h) := (continuous_curvatureDensity n u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)).comp
      (f := fun x : T3 ↦ (h, x)) (continuous_const.prodMk continuous_id)
  have hzero : (∫ x : T3, ∑ j : Fin 3, secondRate n u h j x) = 0 := by
    rw [integral_finsetSum Finset.univ (fun j _ ↦
      (continuous_secondRate n u hu h j).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    simp only [integral_secondRate_eq_zero n u hu h, Finset.sum_const_zero]
  simp only [sum_secondRate_eq n u hu h] at hzero
  rw [integral_add (hd.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))] at hzero
  linarith

def diffusionIntegral (N : ℕ) (u : FourierVelocity) : ℝ :=
  ∫ h : T3, ∫ x : T3, ‖h‖ * ‖H N h‖ * diffusionDensity 1 u h x

def curvatureIntegral (N : ℕ) (u : FourierVelocity) : ℝ :=
  ∫ h : T3, ∫ x : T3, ‖h‖ * ‖H N h‖ * curvatureDensity 1 u h x

theorem integrable_weighted_diffusion (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    Integrable (fun p : T3 × T3 ↦ ‖p.1‖ * ‖H N p.1‖ * diffusionDensity 1 u p.1 p.2)
      ((volume : Measure T3).prod volume) :=
  IntegrableKernelPairing.integrable_mul _ _
    ((PeriodicRieszNearMoment.integrable_firstMoment (d := 3) N).comp_fst (volume : Measure T3))
    ⟨_, continuous_diffusionDensity 1 u hu⟩

theorem integrable_weighted_curvature (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    Integrable (fun p : T3 × T3 ↦ ‖p.1‖ * ‖H N p.1‖ * curvatureDensity 1 u p.1 p.2)
      ((volume : Measure T3).prod volume) :=
  IntegrableKernelPairing.integrable_mul _ _
    ((PeriodicRieszNearMoment.integrable_firstMoment (d := 3) N).comp_fst (volume : Measure T3))
    ⟨_, continuous_curvatureDensity 1 u hu⟩

/-- Exact viscosity contribution for the same angular kernel and exponent
as the stretching payment. No nonnegativity of the curvature is assumed. -/
theorem diffusionIntegral_eq_neg_curvatureIntegral (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) : diffusionIntegral N u = -curvatureIntegral N u := by
  simp only [diffusionIntegral, curvatureIntegral, integral_const_mul,
    integral_diffusion_eq_neg_curvature 1 u hu, mul_neg, integral_neg]

end Mettapedia.FluidDynamics.NavierStokes.LocalWeightedAngularDiffusion
