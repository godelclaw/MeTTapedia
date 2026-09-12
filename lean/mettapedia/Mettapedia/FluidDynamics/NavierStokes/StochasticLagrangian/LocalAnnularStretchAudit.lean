import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularStretchEvolution

/-! Actual annular source, preserved threshold, and material derivative audit. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.FluidDynamics.NavierStokes
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity VorticityAnnularPolynomialSource
open Mettapedia.Analysis

example {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (t : ℝ) (n N : ℕ) (hu : Summable (fourierMoment 3 (s.coefficients t))) :
    VorticityRegularizedSource.source n N (s.coefficients t) = pairedSource n N (s.coefficients t) :=
  source_eq_pairedSource n N _ (summable_fourierMoment_of_le _ (by norm_num : 1 ≤ 3) hu)

example {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (hnu : 0 < nu) (t : ℝ) (N : ℕ) (hu : Summable (fourierMoment 3 (s.coefficients t))) :
    pairedSource 6 N (s.coefficients t) ≤
      (nu / 2) * LocalVorticityEighthMoment.weightedPalinstrophy (s.coefficients t) +
        highAmplitudeSource 6 (VorticityRegularizedIncrement.dissipationThreshold nu)
          N (s.coefficients t) :=
  pairedSource_le_half_dissipation_add_remainder nu hnu N _ hu

example (n : ℕ) (u : FourierVelocity) (nu : ℝ) (x y : UnitAddTorus (Fin 3))
    (v w : Fin 3 → ℝ) : LocalAnnularStretchEvolution.materialPairedRate n 0 u nu x y v w = 0 := by
  simp [LocalAnnularStretchEvolution.materialPairedRate,
    VorticityAnnularKernelTransport.kernelDirectionalRate,
    VorticityAnnularKernelTransport.entryDirectionalRate, AnnularRieszKernel.weight,
    SignedCrossKernel.pairedStretchRate]

#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityAnnularKernelTransport.contDiff_kernel_lift
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityAnnularKernelTransport.hasDerivAt_kernel_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityAnnularKernelTransport.hasDerivAt_kernel_pair_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityAnnularPolynomialSource.pairedSource_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityAnnularPolynomialSource.highAmplitudeSource_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityAnnularPolynomialSource.source_eq_pairedSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityAnnularPolynomialSource.pairedSource_le_half_dissipation_add_remainder
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityAnnularPolynomialSource.tendsto_pairedSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPairedStretchEvolution.hasDerivAt_pairedStretch_path_of_kernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularStretchEvolution.hasDerivAt_pairedStretch_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularStretchEvolution.hasDerivAt_highAmplitudeStretch_path_left
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularStretchEvolution.hasDerivAt_highAmplitudeStretch_path_right
