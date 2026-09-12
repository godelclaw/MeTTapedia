import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSmoothPairedDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticitySmoothAmplitudeSource
import Mettapedia.Analysis.UnitTorusPairIntegration

/-!
# Exact viscosity channel of the smoothly retained annular source

The full vorticity Laplacian acts on both endpoints, including the amplitude
weight. Integration by parts yields minus the complete signed curvature.
The finite annular kernel stays fixed under common translation. This does
not bound the curvature uniformly in cutoff or time.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSmoothAnnularDiffusion

open MeasureTheory
open Mettapedia.Analysis SmoothAmplitudePairing
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalSpatialVorticityJets

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def diffusionDensity (n : ℕ) (L : ℝ) (N : ℕ) (u : FourierVelocity) (x y : T3) : ℝ :=
  retainedEndpointRate (n + 1) L (PeriodicRieszPolynomial.kernel N (x - y))
    (fullVorticity u x) (fullVorticity u y)
    (fullVorticityLaplacian u x) (fullVorticityLaplacian u y)

def curvatureDensity (n : ℕ) (L : ℝ) (N : ℕ) (u : FourierVelocity) (x y : T3) : ℝ :=
  ∑ j : Fin 3, retainedPairCurvature n L (PeriodicRieszPolynomial.kernel N (x - y))
    (fullVorticity u x) (fullVorticity u y) (fullCurlGradient u j x) (fullCurlGradient u j y)

def diffusionSource (n : ℕ) (L : ℝ) (N : ℕ) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3, diffusionDensity n L N u x y

def curvatureSource (n : ℕ) (L : ℝ) (N : ℕ) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3, curvatureDensity n L N u x y

theorem continuous_diffusionDensity (n : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    Continuous (diffusionDensity n L N u).uncurry := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hl := LocalPairedDiffusion.continuous_fullVorticityLaplacian u hu
  exact continuous_retainedEndpointRate (n + 1) L hL
    ((PeriodicRieszPolynomial.continuous_kernel N).comp (continuous_fst.sub continuous_snd))
    (hw.comp continuous_fst) (hw.comp continuous_snd) (hl.comp continuous_fst) (hl.comp continuous_snd)

theorem continuous_curvatureDensity (n : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (curvatureDensity n L N u).uncurry := by
  have hw := continuous_fullVorticity u hu
  exact continuous_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ ↦ continuous_retainedPairCurvature n L hL
    ((PeriodicRieszPolynomial.continuous_kernel N).comp (continuous_fst.sub continuous_snd))
    (hw.comp continuous_fst) (hw.comp continuous_snd)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_fst)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_snd))

theorem diffusionSource_eq_neg_curvatureSource (n : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    diffusionSource n L N u = -curvatureSource n L N u := by
  have he (h : T3) : (∫ x : T3, diffusionDensity n L N u x (x - h)) =
      -(∫ x : T3, curvatureDensity n L N u x (x - h)) := by
    simpa only [diffusionDensity, curvatureDensity, sub_sub_cancel,
      LocalSmoothPairedDiffusion.diffusion, LocalSmoothPairedDiffusion.curvature] using
      LocalSmoothPairedDiffusion.integral_diffusion_eq_neg_curvature n L hL
        (PeriodicRieszPolynomial.kernel N h) u hu h
  rw [diffusionSource, curvatureSource,
    UnitTorusPairIntegration.integral_pair_eq_separation _ (continuous_diffusionDensity n L hL N u hu),
    UnitTorusPairIntegration.integral_pair_eq_separation _
      (continuous_curvatureDensity n L hL N u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu))]
  simp_rw [he]
  rw [integral_neg]
  ring

end Mettapedia.FluidDynamics.NavierStokes.LocalSmoothAnnularDiffusion
