import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxAdjointSectors

/-!
# A squared cancellation factor in the full weighted sector sum

The explicit selected test gains the square of its geometric factor.
All input and output sums are infinite, with the same regularity costs
as the coarse full-test estimate. This does not bound the complementary
test or prove that the selected sector dominates the evolution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxSectorSquareSum

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeHigherDerivativeMoments
open ExchangedFluxAdjointWeightedSum ExchangedFluxAdjointSectors

local notation "H" => Mettapedia.Analysis.UnitTorusGradientProjection.TensorL2
  (Fin 3) (EuclideanSpace ℝ (Fin 3))

theorem sum_weighted_selectedTest_sq_le {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (m : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment (m + 2) u))
    (F : H) (hF : Summable (fun n ↦ weightedOutputNorm (m + 1) F n ^ 2))
    (Q : Finset Wavevector) :
    (∑ q ∈ Q, ‖((1 + ‖frequencyVec q‖) ^ m : ℝ) • selectedTest δ η u F q‖ ^ 2) ≤
      sectorFactor δ η ^ 2 *
        (((54 * (2 * Real.pi)) * (∑' k, weightedCurlNorm (m + 1) u k) ^ 2) ^ 2 *
          ∑' n, weightedOutputNorm (m + 1) F n ^ 2) := by
  have hr := sectorFactor_nonneg hδ hη
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ m + 2) hu
  have h := sum_weighted_series_sq_le m u hu F hF (selectedTerm δ η u F)
    (54 * (2 * Real.pi) * sectorFactor δ η) (by positivity)
    (summable_selectedTerm δ η u hu1 F) (norm_selectedTerm_le hδ hη u F) Q
  exact h.trans_eq (by ring)

theorem summable_weighted_selectedTest_sq {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (m : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment (m + 2) u))
    (F : H) (hF : Summable (fun n ↦ weightedOutputNorm (m + 1) F n ^ 2)) :
    Summable (fun q ↦ ‖((1 + ‖frequencyVec q‖) ^ m : ℝ) • selectedTest δ η u F q‖ ^ 2) :=
  summable_of_sum_le (fun _ ↦ sq_nonneg _) (sum_weighted_selectedTest_sq_le hδ hη m u hu F hF)

theorem tsum_weighted_selectedTest_sq_le {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (m : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment (m + 2) u))
    (F : H) (hF : Summable (fun n ↦ weightedOutputNorm (m + 1) F n ^ 2)) :
    (∑' q, ‖((1 + ‖frequencyVec q‖) ^ m : ℝ) • selectedTest δ η u F q‖ ^ 2) ≤
      sectorFactor δ η ^ 2 *
        (((54 * (2 * Real.pi)) * (∑' k, weightedCurlNorm (m + 1) u k) ^ 2) ^ 2 *
          ∑' n, weightedOutputNorm (m + 1) F n ^ 2) :=
  (summable_weighted_selectedTest_sq hδ hη m u hu F hF).tsum_le_of_sum_le
    (sum_weighted_selectedTest_sq_le hδ hη m u hu F hF)

theorem selectedTerm_zero_parameters (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) : selectedTerm 0 0 u F p q = 0 := by
  apply norm_eq_zero.mp
  have h := norm_selectedTerm_le (le_refl 0) (le_refl 0) u F p q
  exact le_antisymm (by simpa only [sectorFactor, zero_div, mul_zero, zero_add, zero_mul] using h)
    (norm_nonneg _)

theorem selectedTest_zero_parameters (u : FourierVelocity) (F : H) (q : Wavevector) :
    selectedTest 0 0 u F q = 0 := by
  simp only [selectedTest, selectedTerm_zero_parameters, tsum_zero]

/-- Zero thresholds transfer the entire test to the remainder; they do not close its budget. -/
theorem remainderTest_zero_parameters (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (F : H) (q : Wavevector) :
    remainderTest 0 0 u F q = ExchangedFluxAdjointSeries.coefficientTest u F q := by
  have h := coefficientTest_eq_selected_add_remainder 0 0 u hu F q
  simpa only [selectedTest_zero_parameters, zero_add] using h.symm

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxSectorSquareSum
