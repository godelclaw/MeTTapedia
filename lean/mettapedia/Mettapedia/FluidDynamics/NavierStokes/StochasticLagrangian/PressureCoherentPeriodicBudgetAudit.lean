import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergencePeriodization

/-! Wrapped-distance, logarithmic-cost, and changing-direction band checks. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentPeriodicBudgetAudit

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator PancakeBilinearPeriodization
open FourierPressureTraceSymbol
open PressureCoherentDivergencePeriodization
open PressureCoherentDivergenceTruncatedBudget (logarithmicCost)
open PressureLowOutputSymbol (pairEquiv)
open scoped RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example : ‖(fun _ : Fin 6 ↦ ((1 / 2 : ℝ) : UnitAddCircle))‖ = (1 / 2 : ℝ) := by
  rw [pi_norm_const]
  simpa only [abs_one] using AddCircle.norm_half_period_eq (1 : ℝ)

example : logarithmicCost 512 (1 / 2) = 4 := by
  have hn := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  norm_num [logarithmicCost, hn]

def alternatingDirection (j m : ℕ) : R3 :=
  if (j + m) % 2 = 0 then EuclideanSpace.single 0 1 else EuclideanSpace.single 1 1

theorem norm_alternatingDirection (j m : ℕ) : ‖alternatingDirection j m‖ = 1 := by
  unfold alternatingDirection
  split <;> simp

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ J : ℕ,
    Summable (fun j : ℕ ↦ ∑' m, ∫ q : T6,
      ‖q‖ * ‖matchedPeriodicKernel N hN (J + j) m (alternatingDirection (J + j) m) 0 q‖) ∧
    (∑' j : ℕ, ∑' m, ∫ q : T6,
      ‖q‖ * ‖matchedPeriodicKernel N hN (J + j) m (alternatingDirection (J + j) m) 0 q‖) ≤
      C * (1 / 2 : ℝ) ^ J / N * logarithmicCost N (1 / 2) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_high_input_firstMoment_budget
  exact ⟨C, hC, fun N hN J ↦
    (hb N hN J alternatingDirection norm_alternatingDirection 0).2⟩

example (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (i : Fin 3) (k p : Wavevector) :
    ((PressureDyadicPhysicalKernel.physicalCutoff t
        (N⁻¹ • pairEquiv.symm (realFrequency k, realFrequency p)) *
      CoherentPressurePair.tiltPair e (realFrequency k) (realFrequency p) e e i : ℝ) : ℂ) =
      UnitAddTorus.mFourierCoeff (periodicKernel N hN t e i) (pairWavevector k p) *
        ((N⁻¹ * ⟪realFrequency (k + p), e⟫ : ℝ) : ℂ) := by
  simpa only [realFrequency_add, inner_add_left] using retained_pair_eq_mFourierCoeff_mul N hN t e i k p

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentPeriodicBudgetAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.norm_frequencyPairTorus_le_half
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.lintegral_firstMoment_periodize_le_truncated
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.integral_firstMoment_periodize_le_truncated
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceTruncatedBudget.exists_uniform_truncated_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceTruncatedBudget.exists_uniform_matched_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceTruncatedBudget.exists_uniform_output_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceTruncatedBudget.exists_uniform_high_input_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergencePeriodization.retained_pair_eq_mFourierCoeff_mul
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergencePeriodization.integrable_periodicKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergencePeriodization.exists_uniform_output_mass_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergencePeriodization.exists_uniform_high_input_mass_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergencePeriodization.exists_uniform_high_input_firstMoment_budget
