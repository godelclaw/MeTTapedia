import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteBandProjectionAbsorption
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredProjectionViscousBalance

/-!
# The absorbed viscous inequality for an actual filtered solution

The normalization is the same in the positive corrected energy, its
variational gradient, both signed nonlinear work terms, and viscous
absorption. All-input subgrid work is retained. This is not a closed
energy inequality: no nonlinear work budget is supplied or assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredProjectionAbsorption

open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeFilteredStrainDynamics InfiniteFilteredEquation PancakeLocalInfiniteVelocity
open PancakeCoefficientLimitEquation LocalVorticityEighthMoment
open FilteredProjectionMean FilteredProjectionViscousBalance FiniteBandProjectionAbsorption

/-- Both terms use the entire input field in the subgrid difference. -/
def nonlinearWork (ν R : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) : ℝ :=
  work (regularization ν R) (normalization R) P (filteredVelocity χ u)
      (infiniteVelocityRHS 0 (filteredVelocity χ u)) +
    work (regularization ν R) (normalization R) P (filteredVelocity χ u) (subgridForce χ u)

theorem meanCorrectedEnergy_eq (ν R : ℝ) (hν : 0 < ν) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity) :
    meanCorrectedEnergy (regularization ν R) (normalization R) (filteredVelocity χ u) =
      correctedEnergy ν R (filteredVelocity χ u) := by
  exact FilteredProjectionMean.meanCorrectedEnergy_eq _ (regularization_pos ν R hν) _ P _
    (fun q hq ↦ by simp [filteredVelocity, hcut q hq])

theorem correctedEnergy_filtered_bounds (ν R : ℝ) (hν : 0 < ν) (P : Finset Wavevector)
    (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity) :
    meanEnergy (filteredVelocity χ u) / 16 ≤ correctedEnergy ν R (filteredVelocity χ u) ∧
      correctedEnergy ν R (filteredVelocity χ u) ≤ meanEnergy (filteredVelocity χ u) / 8 :=
  correctedEnergy_bounds P _ (fun q hq ↦ by simp [filteredVelocity, hcut q hq]) R hP ν hν

/-- The remaining right-hand side is signed nonlinear work, not an
assumed bound on it. No cutoff-cardinality constant appears. -/
theorem deriv_correctedEnergy_le {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (R : ℝ) (P : Finset Wavevector) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    deriv (fun τ ↦ correctedEnergy ν R (filteredVelocity χ (s.coefficients τ))) t ≤
      nonlinearWork ν R P χ (s.coefficients t) -
        (3 * ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) -
        6 * ν * radialDissipation (filteredVelocity χ (s.coefficients t)) := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ (s.coefficients t) q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have h := deriv_meanCorrectedEnergy_le s hν.le hB _ (regularization_pos ν R hν)
    _ (normalization_pos R) P χ hcut C hχ t ht
  simp_rw [meanCorrectedEnergy_eq ν R hν P χ hcut] at h
  have hp := curvature_payment_le P _ hs R hP ν (normalization R) hν.le
    (normalization_pos R) (absorption_scale_le R)
  unfold nonlinearWork
  linarith only [h, hp]

end Mettapedia.FluidDynamics.NavierStokes.FilteredProjectionAbsorption
