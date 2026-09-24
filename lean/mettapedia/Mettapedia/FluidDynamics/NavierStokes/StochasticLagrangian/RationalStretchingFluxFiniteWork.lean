import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.RationalStretchingFluxHeat

/-! Exact extension of the finite work sum to any proved output cover. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.RationalStretchingFluxFiniteWork

open PeriodicFourierTriad PeriodicTensorParseval PeriodicGradientFluxSymbol
open StretchingFluxCoefficients StretchingFluxFiniteCoefficients
open RationalStretchingFlux RationalStretchingFluxHeat

theorem divergence_eq_zero_of_not_mem (s : Finset Wavevector) (a : RationalVelocity)
    (hs : ∀ q, q ∉ s → a q = 0) (q : Wavevector) (hq : q ∉ outputModes s) :
    rationalDivergenceCoefficient s a q = 0 := by
  have hs' (k : Wavevector) (hk : k ∉ s) : imaginaryLift a k = 0 := by
    ext i
    simp [imaginaryLift, hs k hk]
  have hc : Complex.I * (((2 * Real.pi : ℝ) : ℂ) ^ 4) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (by positivity)))
  ext i
  have h := divergence_imaginaryLift s a hs q i
  have hz : Complex.I * (((2 * Real.pi : ℝ) : ℂ) ^ 4) *
      (rationalDivergenceCoefficient s a q i : ℂ) = 0 := by
    rw [← h]
    simp [coefficients_eq_zero_of_not_mem _ s hs' _ q hq, divergenceCoeff, contraction]
  exact_mod_cast (mul_eq_zero.mp hz).resolve_left hc

theorem heatWork_eq_sum_of_output_subset (s t : Finset Wavevector) (a : RationalVelocity)
    (hs : ∀ q, q ∉ s → a q = 0) (hst : outputModes s ⊆ t) :
    rationalHeatWork s a = ∑ q ∈ t,
      (∑ i, rationalDivergenceCoefficient s a q i * rationalHeatDivergenceCoefficient s a q i) /
        rationalModeSquare q := by
  unfold rationalHeatWork
  apply Finset.sum_subset hst
  intro q _ hq
  simp [divergence_eq_zero_of_not_mem s a hs q hq]

end Mettapedia.FluidDynamics.NavierStokes.RationalStretchingFluxFiniteWork
