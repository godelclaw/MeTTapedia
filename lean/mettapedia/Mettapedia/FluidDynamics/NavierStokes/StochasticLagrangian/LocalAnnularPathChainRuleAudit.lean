import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularMaterialPaths

/-! Audit of the actual interface-inclusive rate and constructed material paths. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.FluidDynamics.NavierStokes Mettapedia.Analysis
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity LocalAnnularSourcePathChainRule

example (n : ℕ) (L : ℝ) (u : FourierVelocity) (nu : ℝ) (x y : UnitAddTorus (Fin 3))
    (v w : Fin 3 → ℝ) : materialHighAmplitudeRate n 0 L u nu x y v w = 0 := by
  simp [materialHighAmplitudeRate, LocalAnnularStretchEvolution.materialPairedRate,
    VorticityAnnularKernelTransport.kernelDirectionalRate,
    VorticityAnnularKernelTransport.entryDirectionalRate, AnnularRieszKernel.weight,
    SignedCrossKernel.pairedStretchRate, SignedCrossKernel.pairedStretch]

#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPathRegularity.absolutelyContinuousOnInterval_fullVorticity_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourcePathChainRule.ae_hasDerivAt_highAmplitudeSource_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourcePathChainRule.integrated_highAmplitudeSource_path_identity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalCompactMaterialPath.exists_locallyLipschitz_materialPath_through
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularMaterialPaths.exists_paths_integrated_source_identity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularMaterialPaths.integral_sourceAlong_eq_initial_add_weighted_rate
#print axioms Mettapedia.Analysis.AbsolutelyContinuousTimeWeight.integral_eq_initial_add_weighted_deriv
#print axioms Mettapedia.Analysis.AbsolutelyContinuousTimeWeight.integral_eq_initial_add_weighted_rate
