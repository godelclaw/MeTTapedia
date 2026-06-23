import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeLinearIncompressibleExamples

/-!
# Picard-Lindelof local coefficient solutions reconstructed as spatial finite-mode velocity fields.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Set
open scoped BigOperators
open scoped ContDiff
open scoped Laplacian

/-- A local coefficient solution supplied by Picard-Lindelof reconstructs to an
actual spatial velocity field whose time derivative is the reconstructed
projected RHS throughout the local interval. -/
theorem finiteModeProjectedNS_local_reconstructed_velocity_exists
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a₀ : FiniteModeState ι) :
    ∃ a : ℝ → FiniteModeState ι, ∃ u : NSVelocityField,
      a 0 = a₀ ∧
        u 0 = finiteModeReconstructedInitialVelocity mode a₀ ∧
          ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x =
              finiteModeReconstructedAcceleration mode C a t x := by
  rcases finiteModeProjectedNSRHS_local_solution_exists C a₀ with
    ⟨a, ha0, ε, hε, ha⟩
  refine ⟨a, finiteModeReconstructedVelocity mode a, ha0, ?_, ε, hε, ?_⟩
  · funext x
    simp [finiteModeReconstructedVelocity, finiteModeReconstructedInitialVelocity, ha0]
  · intro t ht x
    exact finiteModeReconstructedVelocity_timeDerivative_at mode C a t (ha t ht) x

/-- Picard-Lindelof plus divergence-free modes gives a local reconstructed
velocity field with both the projected-RHS time derivative identity and
pointwise incompressibility. -/
theorem finiteModeProjectedNS_local_reconstructed_divergenceFree_velocity_exists
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a₀ : FiniteModeState ι)
    (hmodeDiff : ∀ i x, DifferentiableAt ℝ (mode i) x)
    (hmodeDiv : ∀ i t x, spatialDivergence (fun _ : NSTime => mode i) t x = 0) :
    ∃ a : ℝ → FiniteModeState ι, ∃ u : NSVelocityField,
      a 0 = a₀ ∧
        u 0 = finiteModeReconstructedInitialVelocity mode a₀ ∧
          ∃ ε > (0 : ℝ),
            (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
              timeVelocityDerivative u t x =
                finiteModeReconstructedAcceleration mode C a t x) ∧
            (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
              spatialDivergence u t x = 0) := by
  rcases finiteModeProjectedNSRHS_local_solution_exists C a₀ with
    ⟨a, ha0, ε, hε, ha⟩
  refine ⟨a, finiteModeReconstructedVelocity mode a, ha0, ?_, ε, hε, ?_, ?_⟩
  · funext x
    simp [finiteModeReconstructedVelocity, finiteModeReconstructedInitialVelocity, ha0]
  · intro t ht x
    exact finiteModeReconstructedVelocity_timeDerivative_at mode C a t (ha t ht) x
  · intro t _ht x
    exact finiteModeReconstructedVelocity_spatialDivergence_zero mode a hmodeDiff hmodeDiv t x

end NavierStokes
end FluidDynamics
end Mettapedia
