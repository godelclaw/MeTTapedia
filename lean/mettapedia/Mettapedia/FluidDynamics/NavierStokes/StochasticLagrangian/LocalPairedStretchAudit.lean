import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPairedStretchEvolution
import Mettapedia.Analysis.SignedCrossKernelEvolutionTests

/-! Actual source identification, transported kernel, and signed amplitude-rate audit. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.FluidDynamics.NavierStokes
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity VorticityWeightedStretching VorticityStretchingKernel
open LocalPairedStretchEvolution
open Mettapedia.Analysis.SignedCrossKernel

example {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (t : ℝ) (modes : Finset Wavevector) (hu : Summable (fourierMoment 3 (s.coefficients t))) :
    finiteStretching 6 modes (s.coefficients t) = pairedIntegral 6 modes (s.coefficients t) :=
  finiteStretching_eq_pair 6 modes _
    (summable_fourierMoment_of_le _ (by norm_num : 1 ≤ 3) hu) (s.reality t) (s.transverse t)

example (n : ℕ) (u : FourierVelocity) (nu : ℝ) (x y : UnitAddTorus (Fin 3))
    (v w : Fin 3 → ℝ) : materialPairedRate n ∅ u nu x y v w = 0 := by
  simp [materialPairedRate, kernel, kernelDirectionalRate, pairedStretchRate]

#print axioms Mettapedia.Analysis.RadialPower.hasDerivAt_radialPower_even
#print axioms Mettapedia.Analysis.RadialPower.radialStrainExcess_of_rayleigh
#print axioms Mettapedia.Analysis.RadialPower.evenRadialRate_strain_add
#print axioms Mettapedia.Analysis.SignedCrossKernel.radialPairRate_eq
#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedStretchRate_common_of_equal_rayleigh
#print axioms Mettapedia.Analysis.SignedCrossKernel.hasDerivAt_pairedStretch
#print axioms Mettapedia.Analysis.ODE.hasDerivWithinAt_norm_of_ne_zero
#print axioms Mettapedia.Analysis.SignedCrossKernel.hasDerivAt_highAmplitudeWeight_of_left_lt
#print axioms Mettapedia.Analysis.SignedCrossKernel.hasDerivAt_highAmplitudeWeight_of_right_lt
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityStretchingKernel.hasDerivAt_kernel_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityStretchingKernel.hasDerivAt_kernel_pair_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPairedStretchEvolution.mean_fullStrain_symmetric
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPairedStretchEvolution.hasDerivAt_pairedStretch_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPairedStretchEvolution.hasDerivAt_highAmplitudeStretch_path_left
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPairedStretchEvolution.hasDerivAt_highAmplitudeStretch_path_right
