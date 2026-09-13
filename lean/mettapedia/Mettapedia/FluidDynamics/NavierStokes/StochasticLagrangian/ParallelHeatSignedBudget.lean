import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ParallelHeatGeometry
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalOcticSignedBudget

/-!
# A cutoff-uniform signed residual budget on actual parallel heat flows

The potentially adverse pure curvature need not be paid pointwise. Its signed
time integral is bounded by initial data, uniformly in time and kernel cutoff.
This verifies the distinction between instantaneous monotonicity and a signed
budget on the explicit test family. Arbitrary flows have nonzero stretching;
no budget for that open source is inferred from this example.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ParallelHeatFlow

open scoped ComplexConjugate
open PeriodicFourierTriad PancakeCurlOutputTail

theorem abs_integral_residual_le (ν : ℝ) (hν : 0 ≤ ν)
    (a : Wavevector →₀ ℂ) (ha : IsHorizontal a)
    (hr : ∀ q, a (-q) = conj (a q)) (hz : a 0 = 0)
    (N : ℕ) (ε t : ℝ) (ht : 0 ≤ t) :
    |∫ τ in (0 : ℝ)..t, LocalOcticCorrectedEnergy.residual N ν ε (coefficients ν a τ)| ≤
      45 * |ε| * LocalVorticityEighthMoment.meanEnergy (fun q ↦ vertical (a q)) := by
  let s := solution hν a ha hr hz (t + 1)
  exact LocalOcticSignedBudget.abs_integral_residual_le_of_stretching_zero s
    (fourierMoment 3 (fun q ↦ vertical (a q))) (fourierMoment_nonneg _ _)
    (summable_initial_fourierMoment 3 a)
    (fun _ hτ ↦ fourierMoment_le_initial hν hτ.1 3 a)
    N ε hν (by linarith) (fun τ _ ↦ stretching_coefficients_eq_zero ν a ha τ)
    t ⟨ht, by linarith⟩

end Mettapedia.FluidDynamics.NavierStokes.ParallelHeatFlow
