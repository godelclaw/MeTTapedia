import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ParallelHeatFlow
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalOcticEndpointBalance

/-!
# The actual signed octic balance on parallel heat flows

The solution and every Fourier envelope are constructed from finite horizontal
scalar data. Hence the balance applies on any finite forward interval without
a supplied solution, smoothness envelope, or residual budget. The latter is
still present explicitly in the conclusion.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ParallelHeatFlow

open scoped ComplexConjugate
open PeriodicFourierTriad PancakeCurlOutputTail LocalOcticCorrectedEnergy
open LocalVorticityEighthMoment (weightedPalinstrophy)

theorem corrected_energy_add_half_dissipation_le {ν : ℝ} (hν : 0 ≤ ν)
    (a : Wavevector →₀ ℂ) (ha : IsHorizontal a)
    (hr : ∀ q, a (-q) = conj (a q)) (hz : a 0 = 0)
    (N : ℕ) (ε : ℝ) (hε : |ε| ≤ 1 / 576) (t : ℝ) (ht : 0 ≤ t) :
    energy N ε (coefficients ν a t) + ν / 2 *
        (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (coefficients ν a τ)) ≤
      energy N ε (fun q ↦ vertical (a q)) +
        ∫ τ in (0 : ℝ)..t, residual N ν ε (coefficients ν a τ) := by
  let s := solution hν a ha hr hz (t + 1)
  exact LocalOcticEndpointBalance.energy_add_half_dissipation_le s
    (fourierMoment 3 (fun q ↦ vertical (a q))) (fourierMoment_nonneg _ _)
    (summable_initial_fourierMoment 3 a)
    (fun _ hτ ↦ fourierMoment_le_initial hν hτ.1 3 a)
    N ε hν hε (by linarith) t ⟨ht, by linarith⟩

end Mettapedia.FluidDynamics.NavierStokes.ParallelHeatFlow
