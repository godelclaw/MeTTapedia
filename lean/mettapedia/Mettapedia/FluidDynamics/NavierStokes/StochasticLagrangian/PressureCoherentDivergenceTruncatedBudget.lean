import Mettapedia.Analysis.TruncatedKernelMoment
import Mettapedia.Analysis.GeometricMinSeries
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergencePhysicalKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputSymbol

/-!
# Summable truncated moments for coherent divergence kernels

The full first-moment estimate lacks output-ratio decay. Capping the
displacement cost uses the smaller of that estimate and the kernel mass.
The actual capped moments are summable over all matched output bands,
with an inverse-input-scale gain and an explicit logarithmic loss.
Frozen directions may vary arbitrarily between bands.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceTruncatedBudget

open MeasureTheory Mettapedia.Analysis.TruncatedKernelMoment
open Mettapedia.Analysis.GeometricMinSeries
open PressureLowOutputCutoff (ratio)
open PressureLowOutputDyadicBudget (dyadicParameter dyadicParameter_mem)
open PressureFixedOutputSymbol
open PressureCoherentDivergencePhysicalKernel
open scoped SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

theorem exists_uniform_truncated_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ R : ℝ, 0 ≤ R → ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 → ∀ i : Fin 3,
      moment R (scaledKernel N hN (t, e) i) volume ≤ C * min (R * ratio t) N⁻¹ := by
  obtain ⟨C0, hC0, h0⟩ := exists_uniform_scaled_mass
  obtain ⟨C1, hC1, h1⟩ := exists_uniform_scaled_firstMoment
  let C := max C0 C1
  have hC : 0 ≤ C := hC0.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro N hN R hR t ht e he i
  let K := scaledKernel N hN (t, e) i
  have hK : Integrable K := K.integrable
  have hfirst : Integrable (fun x : E6 ↦ ‖x‖ * ‖K x‖) := by
    simpa only [pow_one] using K.integrable_pow_mul (volume : Measure E6) 1
  rw [mul_min_of_nonneg _ _ hC]
  apply le_min
  · calc
      _ ≤ R * ∫ x : E6, ‖K x‖ := moment_le_mass hR hK
      _ ≤ R * (ratio t * C0) := mul_le_mul_of_nonneg_left (h0 N hN t ht e he i) hR
      _ ≤ R * (ratio t * C) := by
        gcongr
        · exact div_nonneg ht.1 (by norm_num)
        · exact le_max_left _ _
      _ = _ := by ring
  · calc
      _ ≤ ∫ x : E6, ‖x‖ * ‖K x‖ := moment_le_firstMoment hR hK hfirst
      _ ≤ C1 / N := h1 N hN t ht e he i
      _ ≤ C / N := div_le_div_of_nonneg_right (le_max_right _ _) hN.le
      _ = _ := by ring

def matchedKernel (N : ℝ) (hN : 0 < N) (j m : ℕ) (e : R3) (i : Fin 3) : 𝓢(E6, ℂ) :=
  scaledKernel (inputScale N j) (inputScale_pos N hN j) (dyadicParameter (j + m), e) i

theorem inv_inputScale (N : ℝ) (j : ℕ) :
    (inputScale N j)⁻¹ = (1 / 2 : ℝ) ^ j * N⁻¹ := by
  simp only [inputScale, mul_inv_rev, ← inv_pow, one_div]

theorem exists_uniform_matched_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ R : ℝ, 0 ≤ R → ∀ j m : ℕ, ∀ e : R3, ‖e‖ = 1 → ∀ i : Fin 3,
      moment R (matchedKernel N hN j m e i) volume ≤
        C * (1 / 2 : ℝ) ^ j * min ((R / 256) * (1 / 2 : ℝ) ^ m) N⁻¹ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_truncated_bound
  refine ⟨C, hC, fun N hN R hR j m e he i ↦ ?_⟩
  have h := hb (inputScale N j) (inputScale_pos N hN j) R hR
    (dyadicParameter (j + m)) (dyadicParameter_mem _) e he i
  rw [ratio_matched, inv_inputScale] at h
  have heq : R * ((1 / 256 : ℝ) * (1 / 2) ^ j * (1 / 2) ^ m) =
      (1 / 2 : ℝ) ^ j * ((R / 256) * (1 / 2 : ℝ) ^ m) := by ring
  rw [heq, ← mul_min_of_nonneg _ _ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) j)] at h
  exact h.trans_eq (by ring)

def logarithmicCost (N R : ℝ) : ℝ := 3 + Real.log (1 + R * N / 256) / Real.log 2

theorem logarithmicCost_nonneg {N R : ℝ} (hN : 0 ≤ N) (hR : 0 ≤ R) :
    0 ≤ logarithmicCost N R := by
  apply add_nonneg (by norm_num)
  apply div_nonneg
  · exact Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem exists_uniform_output_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ R : ℝ, 0 ≤ R → ∀ j : ℕ, ∀ e : ℕ → R3, (∀ m, ‖e m‖ = 1) → ∀ i : Fin 3,
      Summable (fun m ↦ moment R (matchedKernel N hN j m (e m) i) volume) ∧
      (∑' m, moment R (matchedKernel N hN j m (e m) i) volume) ≤
        C * (1 / 2 : ℝ) ^ j / N * logarithmicCost N R := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_matched_bound
  refine ⟨C, hC, fun N hN R hR j e he i ↦ ?_⟩
  have hA : 0 ≤ R / 256 := div_nonneg hR (by norm_num)
  have hD : 0 ≤ N⁻¹ := inv_nonneg.mpr hN.le
  have hs := summable_min hA hD (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hm := hs.mul_left (C * (1 / 2 : ℝ) ^ j)
  have hle (m : ℕ) := hb N hN R hR j m (e m) (he m) i
  have hk : Summable (fun m ↦ moment R (matchedKernel N hN j m (e m) i) volume) :=
    Summable.of_nonneg_of_le (fun m ↦ moment_nonneg hR _) hle hm
  refine ⟨hk, ?_⟩
  calc
    _ ≤ ∑' m : ℕ, C * (1 / 2 : ℝ) ^ j * min ((R / 256) * (1 / 2 : ℝ) ^ m) N⁻¹ :=
      hk.tsum_le_tsum hle hm
    _ = C * (1 / 2 : ℝ) ^ j * ∑' m : ℕ, min ((R / 256) * (1 / 2 : ℝ) ^ m) N⁻¹ :=
      tsum_mul_left
    _ ≤ C * (1 / 2 : ℝ) ^ j *
        (N⁻¹ * (3 + Real.log (1 + (R / 256) / N⁻¹) / Real.log 2)) :=
      mul_le_mul_of_nonneg_left (tsum_min_half_pow_le hA hD) (by positivity)
    _ = _ := by
      have heq : (R / 256) / N⁻¹ = R * N / 256 := by rw [div_eq_mul_inv, inv_inv]; ring
      rw [heq]
      unfold logarithmicCost
      ring

/-- Both infinite band sums are proved summable before their values are estimated. -/
theorem exists_uniform_high_input_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ R : ℝ, 0 ≤ R → ∀ J : ℕ, ∀ e : ℕ → ℕ → R3,
      (∀ j m, ‖e j m‖ = 1) → ∀ i : Fin 3,
      (∀ j : ℕ, Summable (fun m ↦
        moment R (matchedKernel N hN (J + j) m (e (J + j) m) i) volume)) ∧
      Summable (fun j : ℕ ↦ ∑' m,
        moment R (matchedKernel N hN (J + j) m (e (J + j) m) i) volume) ∧
      (∑' j : ℕ, ∑' m, moment R (matchedKernel N hN (J + j) m (e (J + j) m) i) volume) ≤
        C * (1 / 2 : ℝ) ^ J / N * logarithmicCost N R := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_output_budget
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, fun N hN R hR J e he i ↦ ?_⟩
  have hout (j : ℕ) := hb N hN R hR (J + j) (e (J + j)) (he (J + j)) i
  let B := C * (1 / 2 : ℝ) ^ J / N * logarithmicCost N R
  have hsum := hasSum_geometric_two.mul_left B
  have hle (j : ℕ) : (∑' m,
      moment R (matchedKernel N hN (J + j) m (e (J + j) m) i) volume) ≤ B * (1 / 2 : ℝ) ^ j := by
    exact (hout j).2.trans_eq (by dsimp [B]; rw [pow_add]; ring)
  have hs : Summable (fun j : ℕ ↦ ∑' m,
      moment R (matchedKernel N hN (J + j) m (e (J + j) m) i) volume) :=
    Summable.of_nonneg_of_le (fun j ↦ tsum_nonneg (fun m ↦ moment_nonneg hR _)) hle hsum.summable
  refine ⟨fun j ↦ (hout j).1, hs, ?_⟩
  have h := hs.tsum_le_tsum hle hsum.summable
  rw [hsum.tsum_eq] at h
  exact h.trans_eq (by dsimp [B]; ring)

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceTruncatedBudget
