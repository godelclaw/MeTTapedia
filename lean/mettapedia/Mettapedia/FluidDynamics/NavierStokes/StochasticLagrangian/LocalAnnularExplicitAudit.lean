import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularRateDecomposition
import Mettapedia.Analysis.SignedCrossKernelRateDecompositionTests

/-! Audit of the interface-inclusive spatial source rate and signed channel decomposition. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.FluidDynamics.NavierStokes Mettapedia.Analysis
open PeriodicFourierTriad LocalAnnularExplicitRate LocalAnnularSourcePathChainRule

example (n : ℕ) (L nu : ℝ) (u : FourierVelocity) (x : UnitAddTorus (Fin 3 ⊕ Fin 3)) :
    explicitRate n 0 L nu u x = 0 := by
  simp [explicitRate, materialHighAmplitudeRate, LocalAnnularStretchEvolution.materialPairedRate,
    VorticityAnnularKernelTransport.kernelDirectionalRate,
    VorticityAnnularKernelTransport.entryDirectionalRate, AnnularRieszKernel.weight,
    SignedCrossKernel.pairedStretchRate, SignedCrossKernel.pairedStretch]

#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularWeightDifferentiability.continuous_extendedWeight
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularWeightDifferentiability.locallyLipschitz_extendedWeight
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularWeightDifferentiability.ae_ae_differentiableAt_frozenWeight
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularExplicitRate.hasDerivAt_tangentPath
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularExplicitRate.frozenMaterialRate_eq_of_differentiable
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularExplicitRate.ae_ae_frozenMaterialRate_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularExplicitMean.ae_hasDerivAt_mean
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularExplicitMean.integral_explicitRate_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularExplicitMean.integral_source_eq_initial_add_weighted_rate
#print axioms Mettapedia.Analysis.SignedCrossKernel.highAmplitudeWeightRate_add
#print axioms Mettapedia.Analysis.SignedCrossKernel.highAmplitudeWeightRate_smul
#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedEndpointRate_smul
#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedEndpointRate_self
#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedStretchRate_eq_strain_add_kernel_add_endpoint
#print axioms Mettapedia.Analysis.SignedCrossKernel.highAmplitudeRate_eq_strain_add_kernel_add_endpoint
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularRateDecomposition.explicitRate_eq
#print axioms Mettapedia.Analysis.SignedCrossKernelRateDecompositionTests.negative_kernel_source
#print axioms Mettapedia.Analysis.SignedCrossKernelRateDecompositionTests.radial_decay_rate_positive
