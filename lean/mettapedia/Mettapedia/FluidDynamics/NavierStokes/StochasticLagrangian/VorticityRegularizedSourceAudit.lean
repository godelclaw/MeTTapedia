import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedPayment

/-! The constructed source, its signed split, and its limit at actual solution coefficients. -/

set_option autoImplicit false
noncomputable section

open Filter Mettapedia.FluidDynamics.NavierStokes
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open PancakePeriodicCoherentSplit VorticityRegularizedSource VorticityRegularizedPayment
open LocalLowDiffusionBudget
open VorticityRegularizedIncrement
open scoped Topology

example {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (t : ℝ) (hu : Summable (fourierMoment 3 (s.coefficients t))) :
    Tendsto (fun N : ℕ ↦ source 6 N (s.coefficients t)) atTop
      (𝓝 (LocalVorticityEighthMoment.stretching (s.coefficients t))) :=
  tendsto_eighthMoment_source _ (summable_fourierMoment_of_le _ (by norm_num : 1 ≤ 3) hu)
    (s.reality t) (s.transverse t)

-- The threshold is chosen before the time and frequency cutoff.
example {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (hnu : 0 < nu) :
    ∃ L : ℝ, 0 < L ∧ ∀ (t : ℝ) (N : ℕ), Summable (fourierMoment 3 (s.coefficients t)) →
      source 6 N (s.coefficients t) ≤
        (nu / 2) * LocalVorticityEighthMoment.weightedPalinstrophy (s.coefficients t) +
          highAmplitudeSource 6 L N (s.coefficients t) :=
  ⟨dissipationThreshold nu, dissipationThreshold_pos nu hnu,
    fun _t N hu ↦ source_le_half_dissipation_add_remainder nu hnu N _ hu⟩

example (L : ℝ) (hL : 0 < L) (N : ℕ) (u : FourierVelocity) (x y : UnitAddTorus (Fin 3))
    (hx : fullVorticity u x = 0) :
    Mettapedia.Analysis.SignedCrossKernel.highAmplitudeStretch 6 L
      (Mettapedia.Analysis.PeriodicRieszOperator.kernel N (x - y))
        (fullVorticity u x) (fullVorticity u y) = 0 := by
  apply highAmplitudeStretch_eq_zero_of_endpoint_le L hL N u x y
  exact Or.inl (by rw [hx, norm_zero]; exact hL.le)

example {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (hnu : 0 < nu) (t b : ℝ) (hu : Summable (fourierMoment 3 (s.coefficients t)))
    (hb : ∀ N, highAmplitudeSource 6 (dissipationThreshold nu) N (s.coefficients t) ≤ b) :
    LocalVorticityEighthMoment.stretching (s.coefficients t) ≤
      (nu / 2) * LocalVorticityEighthMoment.weightedPalinstrophy (s.coefficients t) + b :=
  stretching_le_half_dissipation_add_of_remainder_le nu b hnu _ hu
    (s.reality t) (s.transverse t) hb

#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedConvolution.hasSum_curlComponent
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedConvolution.hasSum_entry_convolution
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedQuadratic.symbol_cross_entry_contraction
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedQuadratic.hasSum_quadraticStretch
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedSource.tendsto_quadraticStretch
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedSource.norm_quadraticStretch_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedSource.tendsto_source
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedSource.tendsto_eighthMoment_source
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPairing.integrable_weightedStretch
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPairing.source_eq_pairedSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPairing.tendsto_pairedSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPayment.integrable_pairedStretch
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPayment.integrable_highAmplitudeStretch
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPayment.integrable_bareRadialCost
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPayment.bareRadialIntegral_eq_incrementIntegral
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPayment.abs_source_sub_highAmplitudeSource_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPayment.source_le_half_dissipation_add_remainder
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPayment.highAmplitudeStretch_eq_zero_of_endpoint_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPayment.stretching_le_half_dissipation_add_of_remainder_le
