import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalOcticCorrelation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPairedDiffusion
import Mettapedia.Analysis.UnitTorusPairIntegration

/-!
# Complete signed diffusion of the octic correlation

Common translation fixes the kernel. Periodic integration turns the endpoint
Laplacians into minus the sum of pure and mixed curvature. Only the mixed
curvature is bounded by weighted palinstrophy here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalOcticDiffusion

open MeasureTheory Mettapedia.Analysis OcticKernelCorrelation
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeHaarTransportRate PancakeFourierTranslationCurve
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalSpatialVorticityJets
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def firstRate (H : Op) (u : FourierVelocity) (h : T3) (j : Fin 3) (x : T3) : ℝ :=
  endpointRate H (fullVorticity u x) (fullVorticity u (x - h))
    (fullCurlGradient u j x) (fullCurlGradient u j (x - h))

def secondRate (H : Op) (u : FourierVelocity) (h : T3) (j : Fin 3) (x : T3) : ℝ :=
  endpointRate H (fullVorticity u x) (fullVorticity u (x - h))
      (fullCurlSecond u j x) (fullCurlSecond u j (x - h)) +
    pureCurvature H (fullVorticity u x) (fullVorticity u (x - h))
      (fullCurlGradient u j x) (fullCurlGradient u j (x - h)) +
    mixedCurvature H (fullVorticity u x) (fullVorticity u (x - h))
      (fullCurlGradient u j x) (fullCurlGradient u j (x - h))

theorem continuous_firstRate (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) :
    Continuous (firstRate H u h j) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hg := LocalSquaredGapGradient.continuous_fullCurlGradient u j
  exact continuous_endpointRate continuous_const hw (hw.comp (continuous_id.sub continuous_const))
    hg (hg.comp (continuous_id.sub continuous_const))

theorem continuous_secondRate (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) :
    Continuous (secondRate H u h j) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hg := LocalSquaredGapGradient.continuous_fullCurlGradient u j
  have hs := LocalPairedDiffusion.continuous_fullCurlSecond u j
  exact ((continuous_endpointRate continuous_const hw (hw.comp (continuous_id.sub continuous_const))
    hs (hs.comp (continuous_id.sub continuous_const))).add
      (continuous_pureCurvature continuous_const hw (hw.comp (continuous_id.sub continuous_const))
        hg (hg.comp (continuous_id.sub continuous_const)))).add
      (continuous_mixedCurvature continuous_const hw (hw.comp (continuous_id.sub continuous_const))
        hg (hg.comp (continuous_id.sub continuous_const)))

theorem hasDerivAt_firstRate_shift (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) (x : T3) (t : ℝ) :
    HasDerivAt (fun τ ↦ firstRate H u h j (x + coordinateShift j τ))
      (secondRate H u h j (x + coordinateShift j t)) t := by
  have hs (τ : ℝ) : (x - h) + coordinateShift j τ = (x + coordinateShift j τ) - h := by abel
  have hd := hasDerivAt_endpointRate H
    (hasDerivAt_fullVorticity_shift u hu j x t)
    (hasDerivAt_fullVorticity_shift u hu j (x - h) t)
    (hasDerivAt_fullCurlGradient_shift u hu j x t)
    (hasDerivAt_fullCurlGradient_shift u hu j (x - h) t)
  simpa only [hs, firstRate, secondRate] using hd

theorem integral_secondRate_eq_zero (H : Op) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (h : T3) (j : Fin 3) :
    (∫ x : T3, secondRate H u h j x) = 0 :=
  UnitTorusContinuousRate.integral_rate_eq_zero (firstRate H u h j) (secondRate H u h j)
    (coordinateShift j) (continuous_firstRate H u hu h j) (continuous_secondRate H u hu h j)
    (continuous_coordinateShift j) (coordinateShift_zero j) (hasDerivAt_firstRate_shift H u hu h j)

def diffusionDensity (K : T3 → Op) (u : FourierVelocity) (x y : T3) : ℝ :=
  endpointRate (K (x - y)) (fullVorticity u x) (fullVorticity u y)
    (fullVorticityLaplacian u x) (fullVorticityLaplacian u y)

def pureDensity (K : T3 → Op) (u : FourierVelocity) (x y : T3) : ℝ :=
  ∑ j : Fin 3, pureCurvature (K (x - y)) (fullVorticity u x) (fullVorticity u y)
    (fullCurlGradient u j x) (fullCurlGradient u j y)

def mixedDensity (K : T3 → Op) (u : FourierVelocity) (x y : T3) : ℝ :=
  ∑ j : Fin 3, mixedCurvature (K (x - y)) (fullVorticity u x) (fullVorticity u y)
    (fullCurlGradient u j x) (fullCurlGradient u j y)

theorem continuous_diffusionDensity (K : T3 → Op) (hK : Continuous K)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    Continuous (diffusionDensity K u).uncurry := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hl := LocalPairedDiffusion.continuous_fullVorticityLaplacian u hu
  exact continuous_endpointRate (hK.comp (continuous_fst.sub continuous_snd))
    (hw.comp continuous_fst) (hw.comp continuous_snd) (hl.comp continuous_fst) (hl.comp continuous_snd)

theorem continuous_pureDensity (K : T3 → Op) (hK : Continuous K)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (pureDensity K u).uncurry := by
  have hw := continuous_fullVorticity u hu
  exact continuous_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ ↦ continuous_pureCurvature
    (hK.comp (continuous_fst.sub continuous_snd)) (hw.comp continuous_fst) (hw.comp continuous_snd)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_fst)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_snd))

theorem continuous_mixedDensity (K : T3 → Op) (hK : Continuous K)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (mixedDensity K u).uncurry := by
  have hw := continuous_fullVorticity u hu
  exact continuous_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ ↦ continuous_mixedCurvature
    (hK.comp (continuous_fst.sub continuous_snd)) (hw.comp continuous_fst) (hw.comp continuous_snd)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_fst)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_snd))

theorem integral_separation_balance (K : T3 → Op) (hK : Continuous K)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (h : T3) :
    (∫ x : T3, diffusionDensity K u x (x - h)) +
      (∫ x : T3, pureDensity K u x (x - h)) + (∫ x : T3, mixedDensity K u x (x - h)) = 0 := by
  have hzero : (∫ x : T3, ∑ j : Fin 3, secondRate (K h) u h j x) = 0 := by
    rw [integral_finsetSum Finset.univ (fun j _ ↦
      (continuous_secondRate (K h) u hu h j).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    simp only [integral_secondRate_eq_zero (K h) u hu h, Finset.sum_const_zero]
  have he (x : T3) : (∑ j : Fin 3, secondRate (K h) u h j x) =
      diffusionDensity K u x (x - h) + pureDensity K u x (x - h) + mixedDensity K u x (x - h) := by
    simp only [secondRate, diffusionDensity, pureDensity, mixedDensity, sub_sub_cancel,
      Finset.sum_add_distrib, ← endpointRate_sum, sum_fullCurlSecond u hu]
  simp_rw [he] at hzero
  have hm := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have ht : Continuous (fun x : T3 ↦ (x, x - h)) := continuous_id.prodMk (continuous_id.sub continuous_const)
  have hd : Integrable (fun x : T3 ↦ diffusionDensity K u x (x - h)) :=
    ((continuous_diffusionDensity K hK u hu).comp ht).integrable_of_hasCompactSupport
    (μ := (volume : Measure T3)) (HasCompactSupport.of_compactSpace _)
  have hp : Integrable (fun x : T3 ↦ pureDensity K u x (x - h)) :=
    ((continuous_pureDensity K hK u hm).comp ht).integrable_of_hasCompactSupport
    (μ := (volume : Measure T3)) (HasCompactSupport.of_compactSpace _)
  have hc : Integrable (fun x : T3 ↦ mixedDensity K u x (x - h)) :=
    ((continuous_mixedDensity K hK u hm).comp ht).integrable_of_hasCompactSupport
    (μ := (volume : Measure T3)) (HasCompactSupport.of_compactSpace _)
  have hdp : Integrable (fun x : T3 ↦ diffusionDensity K u x (x - h) + pureDensity K u x (x - h)) :=
    hd.add hp
  rw [integral_add hdp hc, integral_add hd hp] at hzero
  exact hzero

theorem integral_diffusion_eq_neg_curvatures (K : T3 → Op) (hK : Continuous K)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T3, ∫ y : T3, diffusionDensity K u x y) =
      -((∫ x : T3, ∫ y : T3, pureDensity K u x y) +
        (∫ x : T3, ∫ y : T3, mixedDensity K u x y)) := by
  have hm := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hp := continuous_pureDensity K hK u hm
  have hc := continuous_mixedDensity K hK u hm
  have ht : Continuous (fun p : T3 × T3 ↦ (p.2, p.2 - p.1)) :=
    continuous_snd.prodMk (continuous_snd.sub continuous_fst)
  have hip : Integrable (fun h : T3 ↦ ∫ x : T3, pureDensity K u x (x - h)) :=
    ((hp.comp ht).integrable_of_hasCompactSupport (μ := (volume : Measure T3).prod volume)
      (HasCompactSupport.of_compactSpace _)).integral_prod_left
  have hic : Integrable (fun h : T3 ↦ ∫ x : T3, mixedDensity K u x (x - h)) :=
    ((hc.comp ht).integrable_of_hasCompactSupport (μ := (volume : Measure T3).prod volume)
      (HasCompactSupport.of_compactSpace _)).integral_prod_left
  rw [UnitTorusPairIntegration.integral_pair_eq_separation _ (continuous_diffusionDensity K hK u hu),
    UnitTorusPairIntegration.integral_pair_eq_separation _ hp,
    UnitTorusPairIntegration.integral_pair_eq_separation _ hc]
  have he (h : T3) : (∫ x : T3, diffusionDensity K u x (x - h)) =
      -((∫ x : T3, pureDensity K u x (x - h)) + (∫ x : T3, mixedDensity K u x (x - h))) := by
    linarith [integral_separation_balance K hK u hu h]
  simp_rw [he]
  rw [integral_neg, integral_add hip hic]

def pureContribution (N : ℕ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ∫ y : T3, pureDensity (PeriodicRadialRiesz.tensor N) u x y

def diffusionContribution (N : ℕ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ∫ y : T3, diffusionDensity (PeriodicRadialRiesz.tensor N) u x y

theorem integral_mixedDensity_eq (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    (∫ x : T3, ∫ y : T3, mixedDensity (PeriodicRadialRiesz.tensor N) u x y) =
      LocalOcticCorrelation.mixedGradientContribution N u := by
  let f (j : Fin 3) (x y : T3) := mixedCurvature (PeriodicRadialRiesz.tensor N (x - y))
    (fullVorticity u x) (fullVorticity u y) (fullCurlGradient u j x) (fullCurlGradient u j y)
  have hw := continuous_fullVorticity u hu
  have hc (j : Fin 3) : Continuous (f j).uncurry := continuous_mixedCurvature
    ((PeriodicRadialRiesz.continuous_tensor N).comp (continuous_fst.sub continuous_snd))
    (hw.comp continuous_fst) (hw.comp continuous_snd)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_fst)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_snd)
  have hi (j : Fin 3) : Integrable (f j).uncurry ((volume : Measure T3).prod volume) :=
    (hc j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr (j : Fin 3) (x : T3) : Integrable (f j x) :=
    ((hc j).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have ho (j : Fin 3) : Integrable (fun x : T3 ↦ ∫ y : T3, f j x y) :=
    (hi j).integral_prod_left
  change (∫ x : T3, ∫ y : T3, ∑ j : Fin 3, f j x y) = _
  simp_rw [integral_finsetSum _ (fun j _ ↦ hr j _)]
  rw [integral_finsetSum _ (fun j _ ↦ ho j),
    LocalOcticCorrelation.mixedGradientContribution_eq_pairIntegral N u hu]

/-- The whole endpoint viscosity, with the unpaid pure term still explicit. -/
theorem diffusionContribution_eq (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    diffusionContribution N u =
      -(pureContribution N u + LocalOcticCorrelation.mixedGradientContribution N u) := by
  rw [diffusionContribution, integral_diffusion_eq_neg_curvatures _
    (PeriodicRadialRiesz.continuous_tensor N) u hu, integral_mixedDensity_eq N u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)]
  rfl

theorem abs_diffusion_add_pure_le (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    |diffusionContribution N u + pureContribution N u| ≤
      288 * LocalVorticityEighthMoment.weightedPalinstrophy u := by
  rw [diffusionContribution_eq N u hu]
  have he : -(pureContribution N u + LocalOcticCorrelation.mixedGradientContribution N u) +
      pureContribution N u = -LocalOcticCorrelation.mixedGradientContribution N u := by ring
  rw [he, abs_neg]
  exact LocalOcticCorrelation.abs_mixedGradientContribution_le N u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)

theorem correction_mixed_absorption (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (nu ε : ℝ) (hnu : 0 ≤ nu) (hε : |ε| ≤ 1 / 576) :
    |nu * ε * (diffusionContribution N u + pureContribution N u)| ≤
      nu / 2 * LocalVorticityEighthMoment.weightedPalinstrophy u := by
  have hG := LocalVorticityEighthMoment.weightedPalinstrophy_nonneg u
  rw [abs_mul, abs_mul, abs_of_nonneg hnu]
  calc
    _ ≤ nu * |ε| * (288 * LocalVorticityEighthMoment.weightedPalinstrophy u) :=
      mul_le_mul_of_nonneg_left (abs_diffusion_add_pure_le N u hu) (by positivity)
    _ ≤ nu * (1 / 576) * (288 * LocalVorticityEighthMoment.weightedPalinstrophy u) := by
      gcongr
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.LocalOcticDiffusion
