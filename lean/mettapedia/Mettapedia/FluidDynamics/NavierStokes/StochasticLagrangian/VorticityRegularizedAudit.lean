import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedIncrement

/-! The regularized increment budget at actual local-solution coefficients. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.FluidDynamics.NavierStokes
open PeriodicFourierTriad PancakeCurlOutputTail PancakeLocalInfiniteVelocity
open VorticityRegularizedIncrement

example (nu : ℝ) (hnu : 0 < nu) : 0 < dissipationThreshold nu :=
  dissipationThreshold_pos nu hnu

example {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (hnu : 0 < nu) (t : ℝ) (hu : Summable (fourierMoment 3 (s.coefficients t))) :
    ∃ L : ℝ, 0 < L ∧ ∀ N : ℕ,
      2 * L * incrementIntegral N (s.coefficients t) ≤
        (nu / 2) * LocalVorticityEighthMoment.weightedPalinstrophy (s.coefficients t) :=
  ⟨dissipationThreshold nu, dissipationThreshold_pos nu hnu,
    fun N ↦ dissipationThreshold_pays nu hnu.le N _ hu⟩

#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedIncrement.increment_at_displacement_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedIncrement.integrable_increment
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedIncrement.incrementIntegral_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedIncrement.dissipationThreshold_pos
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedIncrement.dissipationThreshold_pays
