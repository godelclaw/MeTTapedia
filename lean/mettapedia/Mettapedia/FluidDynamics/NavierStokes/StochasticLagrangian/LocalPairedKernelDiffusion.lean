import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPairedDiffusion
import Mettapedia.Analysis.UnitTorusPairIntegration

/-!
# Signed paired-source diffusion for a continuous periodic operator kernel

Common translation fixes the separation and therefore the kernel. Integrate
the actual endpoint Laplacians by parts in this direction, then integrate
over separations. The result retains the signed quadratic curvature and
requires no derivative of the kernel. This applies to distinct regularized
kernel families without identifying them.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalPairedKernelDiffusion

open MeasureTheory Mettapedia.Analysis SignedCrossKernel
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalSpatialVorticityJets

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def diffusionDensity (n : ℕ) (K : T3 → Op) (u : FourierVelocity) (x y : T3) : ℝ :=
  pairedEndpointRate (n + 1) (K (x - y)) (fullVorticity u x) (fullVorticity u y)
    (fullVorticityLaplacian u x) (fullVorticityLaplacian u y)

def curvatureDensity (n : ℕ) (K : T3 → Op) (u : FourierVelocity) (x y : T3) : ℝ :=
  ∑ j : Fin 3, pairedCurvature n (K (x - y))
    (fullVorticity u x) (fullVorticity u y) (fullCurlGradient u j x) (fullCurlGradient u j y)

def diffusionSource (n : ℕ) (K : T3 → Op) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3, diffusionDensity n K u x y

def curvatureSource (n : ℕ) (K : T3 → Op) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3, curvatureDensity n K u x y

theorem continuous_diffusionDensity (n : ℕ) (K : T3 → Op) (hK : Continuous K)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    Continuous (diffusionDensity n K u).uncurry := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hl := LocalPairedDiffusion.continuous_fullVorticityLaplacian u hu
  exact continuous_pairedEndpointRate (n + 1) (hK.comp (continuous_fst.sub continuous_snd))
    (hw.comp continuous_fst) (hw.comp continuous_snd) (hl.comp continuous_fst) (hl.comp continuous_snd)

theorem continuous_curvatureDensity (n : ℕ) (K : T3 → Op) (hK : Continuous K)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (curvatureDensity n K u).uncurry := by
  have hw := continuous_fullVorticity u hu
  exact continuous_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ ↦ continuous_pairedCurvature n
    (hK.comp (continuous_fst.sub continuous_snd)) (hw.comp continuous_fst) (hw.comp continuous_snd)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_fst)
    ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).comp continuous_snd))

theorem diffusionSource_eq_neg_curvatureSource (n : ℕ) (K : T3 → Op) (hK : Continuous K)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    diffusionSource n K u = -curvatureSource n K u := by
  have he (h : T3) : (∫ x : T3, diffusionDensity n K u x (x - h)) =
      -(∫ x : T3, curvatureDensity n K u x (x - h)) := by
    simpa only [diffusionDensity, curvatureDensity, sub_sub_cancel,
      LocalPairedDiffusion.diffusion, LocalPairedDiffusion.curvature] using
      LocalPairedDiffusion.integral_diffusion_eq_neg_curvature n (K h) u hu h
  rw [diffusionSource, curvatureSource,
    UnitTorusPairIntegration.integral_pair_eq_separation _ (continuous_diffusionDensity n K hK u hu),
    UnitTorusPairIntegration.integral_pair_eq_separation _
      (continuous_curvatureDensity n K hK u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu))]
  simp_rw [he]
  rw [integral_neg]
  ring

end Mettapedia.FluidDynamics.NavierStokes.LocalPairedKernelDiffusion
