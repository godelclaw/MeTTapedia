import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPairedKernelDiffusion
import Mettapedia.Analysis.PeriodicRieszPolynomial

/-!
# Exact signed curvature of the annular paired-source viscosity channel

Use the actual finite annular kernel and the full vorticity Laplacian.
Endpoint-separation coordinates convert their double spatial integral to
the common-translation identity. No derivative of the kernel is taken.
The curvature is signed; this equality supplies no uniform growth bound.
The amplitude-cutoff source is not silently substituted for this smooth
paired source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAnnularDiffusion

open MeasureTheory
open Mettapedia.Analysis SignedCrossKernel
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalSpatialVorticityJets

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def diffusionDensity (n N : ℕ) (u : FourierVelocity) (x y : T3) : ℝ :=
  pairedEndpointRate (n + 1) (PeriodicRieszPolynomial.kernel N (x - y))
    (fullVorticity u x) (fullVorticity u y)
    (fullVorticityLaplacian u x) (fullVorticityLaplacian u y)

def curvatureDensity (n N : ℕ) (u : FourierVelocity) (x y : T3) : ℝ :=
  ∑ j : Fin 3, pairedCurvature n (PeriodicRieszPolynomial.kernel N (x - y))
    (fullVorticity u x) (fullVorticity u y) (fullCurlGradient u j x) (fullCurlGradient u j y)

def diffusionSource (n N : ℕ) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3, diffusionDensity n N u x y

def curvatureSource (n N : ℕ) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3, curvatureDensity n N u x y

theorem continuous_diffusionDensity (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) : Continuous (diffusionDensity n N u).uncurry := by
  exact LocalPairedKernelDiffusion.continuous_diffusionDensity n
    (PeriodicRieszPolynomial.kernel N) (PeriodicRieszPolynomial.continuous_kernel N) u hu

theorem continuous_curvatureDensity (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : Continuous (curvatureDensity n N u).uncurry := by
  exact LocalPairedKernelDiffusion.continuous_curvatureDensity n
    (PeriodicRieszPolynomial.kernel N) (PeriodicRieszPolynomial.continuous_kernel N) u hu

theorem diffusionSource_eq_neg_curvatureSource (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    diffusionSource n N u = -curvatureSource n N u :=
  LocalPairedKernelDiffusion.diffusionSource_eq_neg_curvatureSource n
    (PeriodicRieszPolynomial.kernel N) (PeriodicRieszPolynomial.continuous_kernel N) u hu

end Mettapedia.FluidDynamics.NavierStokes.LocalAnnularDiffusion
