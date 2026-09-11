import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FrequencyPairTruncatedMoment
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergenceTruncatedBudget

/-!
# Periodic coherent divergence kernels with a logarithmic moment budget

The actual scalar component kernels descend to the unit frequency-pair
torus. Their Fourier coefficients retain the exact longitudinal-frequency
factorization. Their wrapped first moments are summable over both matched
input and output bands, at cost `2^(-J) (1 + log(1 + N)) / N`.
The proof uses bounded wrapped distance, so this conclusion is periodic.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergencePeriodization

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator PancakeBilinearPeriodization
open FrequencyPairPeriodization PressureFixedOutputSymbol
open Mettapedia.Analysis.TruncatedKernelMoment
open PressureLowOutputSymbol (pairEquiv)
open PressureLowOutputCutoff (ratio)
open PressureLowOutputDyadicBudget (dyadicParameter dyadicParameter_mem)
open PressureCoherentDivergencePhysicalKernel
open PressureCoherentDivergenceTruncatedBudget (matchedKernel logarithmicCost)
open scoped FourierTransform SchwartzMap RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T6" => UnitAddTorus (Fin 6)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def periodicKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (i : Fin 3) : T6 → ℂ :=
  periodize (scaledKernel N hN (t, e) i)

theorem measurable_periodicKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (i : Fin 3) :
    Measurable (periodicKernel N hN t e i) :=
  measurable_periodize _ (scaledKernel N hN (t, e) i).continuous.measurable

theorem integrable_periodicKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (i : Fin 3) :
    Integrable (periodicKernel N hN t e i) := integrable_periodize _

theorem integrable_firstMoment (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (i : Fin 3) :
    Integrable (fun q : T6 ↦ ‖q‖ * ‖periodicKernel N hN t e i q‖) := by
  simpa only [pow_one, periodicKernel] using integrable_moment_periodize (scaledKernel N hN (t, e) i) 1

theorem retained_pair_eq_mFourierCoeff_mul
    (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (i : Fin 3) (k p : Wavevector) :
    ((PressureDyadicPhysicalKernel.physicalCutoff t
        (N⁻¹ • pairEquiv.symm (realFrequency k, realFrequency p)) *
      CoherentPressurePair.tiltPair e (realFrequency k) (realFrequency p) e e i : ℝ) : ℂ) =
      UnitAddTorus.mFourierCoeff (periodicKernel N hN t e i) (pairWavevector k p) *
        ((N⁻¹ * (⟪realFrequency k, e⟫ + ⟪realFrequency p, e⟫) : ℝ) : ℂ) := by
  rw [periodicKernel, mFourierCoeff_periodize _ (scaledKernel N hN (t, e) i).continuous.measurable
    (scaledKernel N hN (t, e) i).integrable, ← SchwartzMap.fourier_coe]
  have hfreq : euclideanFrequencyPairOfWavevector (pairWavevector k p) =
      pairEquiv.symm (realFrequency k, realFrequency p) := by
    ext j
    fin_cases j <;> rfl
  rw [hfreq]
  simpa only [pairEquiv.apply_symm_apply] using pressure_eq_fourier_scaledKernel_mul N hN (t, e) i
    (pairEquiv.symm (realFrequency k, realFrequency p))

def matchedPeriodicKernel (N : ℝ) (hN : 0 < N) (j m : ℕ) (e : R3) (i : Fin 3) : T6 → ℂ :=
  periodize (matchedKernel N hN j m e i)

theorem firstMoment_matched_le (N : ℝ) (hN : 0 < N) (j m : ℕ) (e : R3) (i : Fin 3) :
    (∫ q : T6, ‖q‖ * ‖matchedPeriodicKernel N hN j m e i q‖) ≤
      moment (1 / 2) (matchedKernel N hN j m e i) volume :=
  integral_firstMoment_periodize_le_truncated _

theorem exists_uniform_high_input_firstMoment_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ J : ℕ,
      ∀ e : ℕ → ℕ → R3, (∀ j m, ‖e j m‖ = 1) → ∀ i : Fin 3,
      (∀ j : ℕ, Summable (fun m ↦ ∫ q : T6,
        ‖q‖ * ‖matchedPeriodicKernel N hN (J + j) m (e (J + j) m) i q‖)) ∧
      Summable (fun j : ℕ ↦ ∑' m, ∫ q : T6,
        ‖q‖ * ‖matchedPeriodicKernel N hN (J + j) m (e (J + j) m) i q‖) ∧
      (∑' j : ℕ, ∑' m, ∫ q : T6,
        ‖q‖ * ‖matchedPeriodicKernel N hN (J + j) m (e (J + j) m) i q‖) ≤
        C * (1 / 2 : ℝ) ^ J / N * logarithmicCost N (1 / 2) := by
  obtain ⟨C, hC, hb⟩ := PressureCoherentDivergenceTruncatedBudget.exists_uniform_high_input_budget
  refine ⟨C, hC, fun N hN J e he i ↦ ?_⟩
  obtain ⟨hinner, houter, hbound⟩ := hb N hN (1 / 2) (by norm_num) J e he i
  have hle (j m : ℕ) := firstMoment_matched_le N hN (J + j) m (e (J + j) m) i
  have hs (j : ℕ) : Summable (fun m ↦ ∫ q : T6,
      ‖q‖ * ‖matchedPeriodicKernel N hN (J + j) m (e (J + j) m) i q‖) :=
    Summable.of_nonneg_of_le (fun m ↦ integral_nonneg (fun q ↦ by positivity)) (hle j) (hinner j)
  have hj (j : ℕ) := (hs j).tsum_le_tsum (hle j) (hinner j)
  have ht : Summable (fun j : ℕ ↦ ∑' m, ∫ q : T6,
      ‖q‖ * ‖matchedPeriodicKernel N hN (J + j) m (e (J + j) m) i q‖) :=
    Summable.of_nonneg_of_le
      (fun j ↦ tsum_nonneg (fun m ↦ integral_nonneg (fun q ↦ by positivity))) hj houter
  exact ⟨hs, ht, (ht.tsum_le_tsum hj houter).trans hbound⟩

theorem exists_uniform_output_mass_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ j : ℕ,
      ∀ e : ℕ → R3, (∀ m, ‖e m‖ = 1) → ∀ i : Fin 3,
      Summable (fun m ↦ ∫ q : T6, ‖matchedPeriodicKernel N hN j m (e m) i q‖) ∧
      (∑' m, ∫ q : T6, ‖matchedPeriodicKernel N hN j m (e m) i q‖) ≤
        C * (1 / 2 : ℝ) ^ j := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_scaled_mass
  refine ⟨C / 128, div_nonneg hC (by norm_num), fun N hN j e he i ↦ ?_⟩
  have hle (m : ℕ) : (∫ q : T6, ‖matchedPeriodicKernel N hN j m (e m) i q‖) ≤
      (C / 256 * (1 / 2 : ℝ) ^ j) * (1 / 2 : ℝ) ^ m := by
    have h := integral_moment_periodize_le (matchedKernel N hN j m (e m) i) 0
    simp only [pow_zero, one_mul] at h
    exact (h.trans (hb (inputScale N j) (inputScale_pos N hN j)
      _ (dyadicParameter_mem _) (e m) (he m) i)).trans_eq (by rw [ratio_matched]; ring)
  have hsum := hasSum_geometric_two.mul_left (C / 256 * (1 / 2 : ℝ) ^ j)
  have hs : Summable (fun m ↦ ∫ q : T6, ‖matchedPeriodicKernel N hN j m (e m) i q‖) :=
    Summable.of_nonneg_of_le (fun m ↦ integral_nonneg (fun q ↦ norm_nonneg _)) hle hsum.summable
  refine ⟨hs, ?_⟩
  have h := hs.tsum_le_tsum hle hsum.summable
  rw [hsum.tsum_eq] at h
  exact h.trans_eq (by ring)

theorem exists_uniform_high_input_mass_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ J : ℕ,
      ∀ e : ℕ → ℕ → R3, (∀ j m, ‖e j m‖ = 1) → ∀ i : Fin 3,
      (∀ j : ℕ, Summable (fun m ↦ ∫ q : T6,
        ‖matchedPeriodicKernel N hN (J + j) m (e (J + j) m) i q‖)) ∧
      Summable (fun j : ℕ ↦ ∑' m, ∫ q : T6,
        ‖matchedPeriodicKernel N hN (J + j) m (e (J + j) m) i q‖) ∧
      (∑' j : ℕ, ∑' m, ∫ q : T6,
        ‖matchedPeriodicKernel N hN (J + j) m (e (J + j) m) i q‖) ≤ C * (1 / 2 : ℝ) ^ J := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_output_mass_budget
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, fun N hN J e he i ↦ ?_⟩
  have hout (j : ℕ) := hb N hN (J + j) (e (J + j)) (he (J + j)) i
  have hsum := hasSum_geometric_two.mul_left (C * (1 / 2 : ℝ) ^ J)
  have hle (j : ℕ) : (∑' m, ∫ q : T6,
      ‖matchedPeriodicKernel N hN (J + j) m (e (J + j) m) i q‖) ≤
        (C * (1 / 2 : ℝ) ^ J) * (1 / 2 : ℝ) ^ j := by
    exact (hout j).2.trans_eq (by rw [pow_add]; ring)
  have hs : Summable (fun j : ℕ ↦ ∑' m, ∫ q : T6,
      ‖matchedPeriodicKernel N hN (J + j) m (e (J + j) m) i q‖) :=
    Summable.of_nonneg_of_le
      (fun j ↦ tsum_nonneg (fun m ↦ integral_nonneg (fun q ↦ norm_nonneg _))) hle hsum.summable
  refine ⟨fun j ↦ (hout j).1, hs, ?_⟩
  have h := hs.tsum_le_tsum hle hsum.summable
  rw [hsum.tsum_eq] at h
  exact h.trans_eq (by ring)

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergencePeriodization
