import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputSymbol
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressurePeriodicEnvelope

/-!
# Common envelopes for fixed-output pressure kernels

For input scale `N * 2^j`, summing the output bands starting at index `j`
retains a `4^(-j)` gain in both mass and first moment. The majorant is
independent of the frozen direction, and its domination holds on one
full-measure set for every input and output index.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputEnvelope

open MeasureTheory PressureFixedOutputSymbol PressurePeriodicEnvelope PressureDyadicPeriodization
open PressureLowOutputDyadicBudget PressureLowOutputCutoff

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem hasSum_quarter : HasSum (fun j : ℕ ↦ (1 / 4 : ℝ) ^ j) (4 / 3 : ℝ) := by
  convert hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) using 1
  norm_num

theorem exists_uniform_envelope :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∃ M : (N : ℝ) → 0 < N → ℕ → ℕ → T6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N,
        (∀ j m, (∀ q, 0 ≤ M N hN j m q) ∧ Measurable (M N hN j m) ∧
          Integrable (M N hN j m) ∧ Integrable (fun q ↦ ‖q‖ * M N hN j m q)) ∧
        (∀ᵐ q : T6, ∀ j m : ℕ, ∀ e : R3, ‖e‖ = 1 →
          ‖periodicKernel (inputScale N j) (inputScale_pos N hN j)
            (dyadicParameter (j + m)) e q‖ ≤ M N hN j m q) ∧
        (∀ j, Summable (fun m ↦ ∫ q : T6, M N hN j m q) ∧
          (∑' m, ∫ q : T6, M N hN j m q) ≤ C0 * (1 / 4 : ℝ) ^ j ∧
          Summable (fun m ↦ ∫ q : T6, ‖q‖ * M N hN j m q) ∧
          (∑' m, ∫ q : T6, ‖q‖ * M N hN j m q) ≤ (C1 / N) * (1 / 4 : ℝ) ^ j) := by
  obtain ⟨C0, C1, hC0, hC1, M, hb⟩ := exists_uniform_periodic_envelope
  refine ⟨C0 / 49152, C1 / 128, div_nonneg hC0 (by norm_num),
    div_nonneg hC1 (by norm_num),
    fun N hN j m ↦ M (inputScale N j) (inputScale_pos N hN j) (dyadicParameter (j + m)), ?_⟩
  intro N hN
  have h (j m : ℕ) := hb (inputScale N j) (inputScale_pos N hN j) _
    (dyadicParameter_mem (j + m))
  refine ⟨fun j m ↦ ⟨(h j m).1, (h j m).2.1, (h j m).2.2.1, (h j m).2.2.2.1⟩,
    ae_all_iff.mpr (fun j ↦ ae_all_iff.mpr (fun m ↦ (h j m).2.2.2.2.1)), ?_⟩
  intro j
  have hmass (m : ℕ) : (∫ q : T6, M (inputScale N j) (inputScale_pos N hN j)
      (dyadicParameter (j + m)) q) ≤
      ((C0 / 65536) * (1 / 4 : ℝ) ^ j) * (1 / 4 : ℝ) ^ m :=
    ((h j m).2.2.2.2.2.1).trans_eq (by rw [ratio_sq_matched]; ring)
  have hmom (m : ℕ) : (∫ q : T6, ‖q‖ * M (inputScale N j) (inputScale_pos N hN j)
      (dyadicParameter (j + m)) q) ≤
      ((C1 / (256 * N)) * (1 / 4 : ℝ) ^ j) * (1 / 2 : ℝ) ^ m :=
    ((h j m).2.2.2.2.2.2).trans_eq (by rw [ratio_div_inputScale]; ring)
  have hs0 := hasSum_quarter.mul_left ((C0 / 65536) * (1 / 4 : ℝ) ^ j)
  have hs1 := hasSum_geometric_two.mul_left ((C1 / (256 * N)) * (1 / 4 : ℝ) ^ j)
  have hi0 := Summable.of_nonneg_of_le
    (fun m ↦ integral_nonneg (h j m).1) hmass hs0.summable
  have hi1 := Summable.of_nonneg_of_le
    (fun m ↦ integral_nonneg (fun q ↦ mul_nonneg (norm_nonneg q) ((h j m).1 q)))
    hmom hs1.summable
  refine ⟨hi0, ?_, hi1, ?_⟩
  · exact (hi0.tsum_le_tsum hmass hs0.summable).trans_eq (by rw [hs0.tsum_eq]; ring)
  · exact (hi1.tsum_le_tsum hmom hs1.summable).trans_eq (by rw [hs1.tsum_eq]; ring)

end Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputEnvelope
