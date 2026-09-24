import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDirectionFreezing
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootOperatorBudget

/-!
# Actual adaptive-root freezing of the high-input pressure field

The cover is constructed from the actual strain and vorticity. Its weighted
unoriented-line error pays for changing the moving direction to the frozen
patch directions. The field-size cost remains explicit; no time budget is
assumed or concluded.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootDirectionFreezing

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeSpectralFiniteDifference
open PancakeHigherDerivativeMoments LocalLowDiffusionBudget LocalGaussianPressurePartition
open GaussianRootVorticity GaussianRootPartition GaussianRootOperatorBudget AdaptiveGaussianLinePartition
open PressureHighInputAction PressureDirectionFreezing

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)

theorem exists_local_root_transfer :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ J : ℕ,
      ∀ gamma : ℝ, 0 < gamma → ∀ chi : Wavevector → ℂ, ∀ modes : Finset Wavevector,
      ∀ u : FourierVelocity, ∀ hu : Summable (fourierMoment 2 u), ∀ rho : ℝ, 0 < rho →
      ∃ centers : Finset T3, centers.Nonempty ∧
      let tau := temperature centers.card rho
      let c := rootPatch gamma chi modes u centers tau
      let w := complexVorticityField u (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu)
      0 < tau ∧ ∀ x : T3,
        QuarticGapTiltWeight.weight gamma (spatialStrain modes (filteredVelocity chi u) x)
          (fullVorticity u x) * ‖tailOperator N hN J (localDirection chi modes u x) w w x‖ ^ 2 ≤
        2 * (∑ i : ↑centers, c i x ^ 4 * ‖tailOperator N hN J (localDirection chi modes u i.1) w w x‖ ^ 2) +
          2 * (C * (1 / 4 : ℝ) ^ J) ^ 2 * ‖w‖ ^ 4 * rho ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_weighted_bound
  refine ⟨C, hC, ?_⟩
  intro N hN J gamma hg chi modes u hu rho hrho
  obtain ⟨centers, hc, ht, _, hcoverage, hline, _⟩ :=
    exists_local_root_partition gamma hg chi modes u hu rho hrho
  refine ⟨centers, hc, ht, ?_⟩
  intro x
  let w := complexVorticityField u (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu)
  have h := hb N hN J ↑centers (localDirection chi modes u x) (topVector_norm _)
    (fun i : ↑centers ↦ localDirection chi modes u i.1) (fun _ ↦ topVector_norm _)
    w w (fun i ↦ rootPatch gamma chi modes u centers (temperature centers.card rho) i x ^ 4)
    (fun _ ↦ by positivity) x
  rw [hcoverage x] at h
  have htail := mul_le_mul_of_nonneg_left (hline x)
    (show 0 ≤ 2 * (C * (1 / 4 : ℝ) ^ J) ^ 2 * ‖w‖ ^ 2 * ‖w‖ ^ 2 by positivity)
  have hfinal := h.trans (add_le_add le_rfl htail)
  convert hfinal using 1 <;> first | rfl | ring

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootDirectionFreezing
