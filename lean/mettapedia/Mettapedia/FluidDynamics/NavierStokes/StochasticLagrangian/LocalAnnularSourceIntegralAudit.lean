import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularSourceIntegral
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularSourcePathIntegral

/-! Signed integrated budget and interface-safe actual-source path audit. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.FluidDynamics.NavierStokes
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity VorticityAnnularPolynomialSource LocalVorticityEighthMoment
open LocalAnnularSourceIntegral VorticityRegularizedIncrement

example {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (hnu : 0 < nu) (hT : 0 < T) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hbudget : ∀ N, (∫ τ in (0 : ℝ)..t,
      highAmplitudeSource 6 (dissipationThreshold nu) N (s.coefficients τ)) ≤ 0) :
    meanEnergy (s.coefficients t) / 8 +
      nu / 2 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) ≤ meanEnergy u₀ / 8 := by
  simpa only [add_zero] using
    energy_add_half_dissipation_le_of_remainder_integral_le s g hg hSum hu hnu hT t ht 0 hbudget

example (n N : ℕ) (L : ℝ) (u : FourierVelocity) :
    highAmplitudeSource n L N u = VorticityRegularizedPayment.highAmplitudeSource n L N u :=
  highAmplitudeSource_eq n L N u

#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourceContinuity.continuousOn_pairIntegral
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourceContinuity.continuous_pairedDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourceContinuity.continuous_highAmplitudeDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourceContinuity.continuousOn_pairedSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourceContinuity.continuousOn_highAmplitudeSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedSource.norm_strainCoeff_le_firstMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedSource.tsum_norm_strainCoeff_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedSource.norm_source_six_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedSource.norm_source_six_le_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourceIntegral.intervalIntegrable_pairedSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourceIntegral.intervalIntegrable_highAmplitudeSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourceIntegral.tendsto_integral_pairedSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourceIntegral.integral_stretching_le_of_remainder_integral_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourceIntegral.energy_add_half_dissipation_le_of_remainder_integral_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourcePathIntegral.absolutelyContinuousOnInterval_highAmplitudeSource_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourcePathIntegral.intervalIntegrable_deriv_highAmplitudeSource_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourcePathIntegral.integral_deriv_highAmplitudeSource_path_eq_sub
