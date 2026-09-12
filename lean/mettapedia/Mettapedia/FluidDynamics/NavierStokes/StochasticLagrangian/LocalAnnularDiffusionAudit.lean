import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularDiffusion
import Mettapedia.Analysis.SignedCrossKernelCurvatureTests

/-! Audit of the actual common-translation curvature identity, before amplitude cutoff. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.Analysis
open Mettapedia.FluidDynamics.NavierStokes PeriodicFourierTriad LocalAnnularDiffusion

example (n : ℕ) (u : FourierVelocity) : diffusionSource n 0 u = 0 := by
  simp [diffusionSource, diffusionDensity, SignedCrossKernel.pairedEndpointRate]

example (n : ℕ) (u : FourierVelocity) : curvatureSource n 0 u = 0 := by
  simp [curvatureSource, curvatureDensity, SignedCrossKernel.pairedCurvature]

#print axioms Mettapedia.Analysis.RadialPower.hasDerivAt_evenRadialRate
#print axioms Mettapedia.Analysis.SignedCrossKernel.hasDerivAt_pairedStretch_constKernel
#print axioms Mettapedia.Analysis.SignedCrossKernel.hasDerivAt_pairedEndpointRate
#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedEndpointRate_sum
#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedCurvature_self
#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedCurvature_collinear
#print axioms Mettapedia.Analysis.UnitTorusContinuousRate.integral_rate_eq_zero
#print axioms Mettapedia.Analysis.UnitTorusPairIntegration.integral_pair_eq_separation
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPairedDiffusion.hasDerivAt_firstRate_shift
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPairedDiffusion.integral_secondRate_eq_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPairedDiffusion.sum_secondRate_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPairedDiffusion.integral_diffusion_eq_neg_curvature
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularDiffusion.continuous_diffusionDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularDiffusion.continuous_curvatureDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularDiffusion.diffusionSource_eq_neg_curvatureSource
#print axioms Mettapedia.Analysis.SignedCrossKernelCurvatureTests.curvature_radial_value
