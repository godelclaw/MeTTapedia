import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergenceEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FrequencyPairRelativeMoment
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentChannelPeriodization

/-!
# Relative displacement moments retain the low-output ratio

The long common displacement cancels in the difference of the two input
locations. Every relative moment of order `m` therefore retains the mass
factor `ratio(t)` and gains `N⁻ᵐ`, without an inverse-ratio loss.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentRelativeMoment

open MeasureTheory Mettapedia.Analysis.DensityLinearChange
open Mettapedia.Analysis.SchwartzLinearChange Mettapedia.Analysis.SchwartzDilation
open PressureLowOutputCutoff (ratio)
open PressureLowOutputSymbol (pairEquiv)
open PressureLowOutputChange PressureCoherentDivergenceEnvelope
open FrequencyPairPeriodization FrequencyPairEnvelope
open PressureCoherentChannelPeriodization (periodicKernel)
open PressureCoherentDivergenceChannel (Factor)
open PressureCoherentDivergenceOperatorKernel (operatorKernel)
open PancakeBilinearPeriodization (firstTorusDisplacement secondTorusDisplacement)
open scoped NNReal

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

theorem relativeDisplacement_spatialChange_symm (rho : ℝ) (hr : rho ≠ 0) (x : E6) :
    relativeDisplacement ((spatialChange rho hr).symm x) = (pairEquiv x).1 := by
  simp [relativeDisplacement, spatialChange_symm_apply]

theorem relativeDisplacement_dilation_symm (N : ℝ) (hN : N ≠ 0) (x : E6) :
    relativeDisplacement ((dilationEquiv N hN).symm x) = N⁻¹ • relativeDisplacement x := by
  simp [relativeDisplacement, dilationEquiv_symm_apply, map_smul, smul_sub]

theorem integral_relativeMoment_physicalEnvelope (H : E6 → ℝ) (t : ℝ) (m : ℕ) :
    (∫ x : E6, ‖relativeDisplacement x‖ ^ m * physicalEnvelope H t x) =
      |ratio t| * ∫ x : E6, ‖(pairEquiv x).1‖ ^ m * H x := by
  by_cases hr : ratio t = 0
  · simp [physicalEnvelope, hr]
  · rw [physicalEnvelope, dif_neg hr, integral_mul_pullbackDensity]
    simp_rw [relativeDisplacement_spatialChange_symm, mul_left_comm _ |ratio t|]
    exact integral_const_mul _ _

theorem integral_relativeMoment_scaledEnvelope (H : E6 → ℝ) (N : ℝ) (hN : 0 < N)
    (t : ℝ) (m : ℕ) :
    (∫ x : E6, ‖relativeDisplacement x‖ ^ m * scaledEnvelope H N hN t x) =
      |ratio t| * N⁻¹ ^ m * ∫ x : E6, ‖(pairEquiv x).1‖ ^ m * H x := by
  rw [scaledEnvelope, integral_mul_pullbackDensity]
  simp only [relativeDisplacement_dilation_symm, norm_smul, mul_pow, Real.norm_eq_abs,
    abs_inv, abs_of_pos hN]
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_relativeMoment_physicalEnvelope]
  ring

theorem integrable_firstCoordinateMoment (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x) (hHc : Continuous H)
    (m : ℕ) (hHm : Integrable (fun x ↦ ‖x‖ ^ m * H x)) :
    Integrable (fun x : E6 ↦ ‖(pairEquiv x).1‖ ^ m * H x) := by
  apply hHm.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (hH x))]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_first_le x) m) (hH x)

theorem integrable_relativeMoment_physicalEnvelope (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x)
    (hHc : Continuous H) (m : ℕ) (hHm : Integrable (fun x ↦ ‖x‖ ^ m * H x)) (t : ℝ) :
    Integrable (fun x : E6 ↦ ‖relativeDisplacement x‖ ^ m * physicalEnvelope H t x) := by
  by_cases hr : ratio t = 0
  · simp [physicalEnvelope, hr]
  · rw [physicalEnvelope, dif_neg hr]
    apply integrable_mul_pullbackDensity
    simp_rw [relativeDisplacement_spatialChange_symm, mul_left_comm _ |ratio t|]
    exact (integrable_firstCoordinateMoment H hH hHc m hHm).const_mul _

theorem integrable_relativeMoment_scaledEnvelope (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x)
    (hHc : Continuous H) (m : ℕ) (hHm : Integrable (fun x ↦ ‖x‖ ^ m * H x))
    (N : ℝ) (hN : 0 < N) (t : ℝ) :
    Integrable (fun x : E6 ↦ ‖relativeDisplacement x‖ ^ m * scaledEnvelope H N hN t x) := by
  rw [scaledEnvelope]
  apply integrable_mul_pullbackDensity
  simp only [relativeDisplacement_dilation_symm, norm_smul, mul_pow, Real.norm_eq_abs,
    abs_inv, abs_of_pos hN]
  simpa only [mul_assoc] using
    (integrable_relativeMoment_physicalEnvelope H hH hHc m hHm t).const_mul (N⁻¹ ^ m)

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3
local notation "T6" => UnitAddTorus (Fin 6)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem exists_uniform_envelope (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M : (N : ℝ) → 0 < N → ℝ → E6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N, ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
        (∀ x, 0 ≤ M N hN t x) ∧ Continuous (M N hN t) ∧ Integrable (M N hN t) ∧
        Integrable (fun x ↦ ‖relativeDisplacement x‖ ^ m * M N hN t x) ∧
        (∀ e : R3, ‖e‖ = 1 → ∀ c : Factor, ∀ x, ‖operatorKernel N hN t e c x‖ ≤ M N hN t x) ∧
        (∫ x : E6, M N hN t x) ≤ ratio t * C ∧
        (∫ x : E6, ‖relativeDisplacement x‖ ^ m * M N hN t x) ≤ ratio t * C / N ^ m := by
  obtain ⟨H, hn, hc, hi, hm, hb⟩ := PressureCoherentDivergenceChannel.exists_uniform_envelope m
  let C := 3 * max (∫ x : E6, H x) (∫ x : E6, ‖x‖ ^ m * H x)
  have hC : 0 ≤ C := mul_nonneg (by norm_num)
    ((integral_nonneg hn).trans (le_max_left _ _))
  have hfirst : (∫ x : E6, ‖(pairEquiv x).1‖ ^ m * H x) ≤ ∫ x : E6, ‖x‖ ^ m * H x := by
    apply integral_mono (integrable_firstCoordinateMoment H hn hc m hm) hm
    intro x
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_first_le x) m) (hn x)
  refine ⟨C, hC, fun N hN t x ↦ 3 * scaledEnvelope H N hN t x, fun N hN t ht ↦ ?_⟩
  have hp := physicalEnvelope_nonneg H hn t
  have hr : 0 ≤ ratio t := div_nonneg ht.1 (by norm_num)
  refine ⟨fun x ↦ mul_nonneg (by norm_num) (pullbackDensity_nonneg _ _ hp x),
    continuous_const.mul (continuous_pullbackDensity _ _ (continuous_physicalEnvelope H hc t)),
    (integrable_pullbackDensity _ _ (integrable_physicalEnvelope H hi t)).const_mul 3, ?_, ?_, ?_, ?_⟩
  · simpa only [mul_left_comm] using (integrable_relativeMoment_scaledEnvelope H hn hc m hm N hN t).const_mul 3
  · intro e he c x
    exact PressureCoherentDivergenceOperatorKernel.norm_operatorKernel_le N hN t e he c
      (scaledEnvelope H N hN t) (fun i ↦ norm_scaledKernel_le H N hN t e c i (hb t ht e he c i)) x
  · rw [integral_const_mul, mass_scaledEnvelope, abs_of_nonneg hr]
    have h := mul_le_mul_of_nonneg_left (le_max_left (∫ x : E6, H x) (∫ x : E6, ‖x‖ ^ m * H x))
      (show 0 ≤ 3 * ratio t by positivity)
    simpa only [C, mul_assoc, mul_left_comm] using h
  · simp_rw [mul_left_comm (‖_‖ ^ m) (3 : ℝ)]
    rw [integral_const_mul, integral_relativeMoment_scaledEnvelope, abs_of_nonneg hr]
    have h := mul_le_mul_of_nonneg_left
      (hfirst.trans (le_max_right (∫ x : E6, H x) (∫ x : E6, ‖x‖ ^ m * H x)))
      (show 0 ≤ 3 * ratio t * N⁻¹ ^ m by positivity)
    calc
      _ = (3 * ratio t * N⁻¹ ^ m) * (∫ x : E6, ‖(pairEquiv x).1‖ ^ m * H x) := by ring
      _ ≤ (3 * ratio t * N⁻¹ ^ m) * max (∫ x : E6, H x) (∫ x : E6, ‖x‖ ^ m * H x) := h
      _ = ratio t * C / N ^ m := by dsimp [C]; ring

/-- One envelope controls all directions and channels, while every prescribed
relative moment retains the frequency ratio, including after periodization. -/
theorem exists_uniform_periodic_envelope (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M : (N : ℝ) → 0 < N → ℝ → T6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N, ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
        (∀ q, 0 ≤ M N hN t q) ∧ Measurable (M N hN t) ∧ Integrable (M N hN t) ∧
        Integrable (fun q ↦ ‖relativeTorusDisplacement q‖ ^ m * M N hN t q) ∧
        (∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 → ∀ c : Factor,
          ‖periodicKernel N hN t e c q‖ ≤ M N hN t q) ∧
        (∫ q : T6, M N hN t q) ≤ ratio t * C ∧
        (∫ q : T6, ‖relativeTorusDisplacement q‖ ^ m * M N hN t q) ≤
          ratio t * C * min ((1 / 2 : ℝ) ^ m) (N⁻¹ ^ m) := by
  obtain ⟨C, hC, H, hb⟩ := exists_uniform_envelope m
  refine ⟨C, hC, fun N hN t ↦ periodize (H N hN t), fun N hN t ht ↦ ?_⟩
  obtain ⟨hn, hc, hi, hm, hk, hmass, hmom⟩ := hb N hN t ht
  have hp := periodize_nonneg _ hn
  have hip : Integrable (periodize (H N hN t)) := by
    simpa only [pow_zero, one_mul] using
      FrequencyPairEnvelope.integrable_moment_periodize _ hn hc.measurable 0 (by simpa using hi)
  have him := integrable_relativeMoment_periodize _ hn hc.measurable m hm
  have hmp : (∫ q : T6, periodize (H N hN t) q) ≤ ratio t * C := by
    have h := FrequencyPairEnvelope.integral_moment_periodize_le _ hn hc.measurable 0
      (by simpa using hi)
    simp only [pow_zero, one_mul] at h
    exact h.trans hmass
  refine ⟨hp, measurable_periodize _ hc.measurable, hip, him, ?_, hmp, ?_⟩
  · have h := ae_norm_periodize_family_le
      (fun a : {e : R3 // ‖e‖ = 1} × Factor ↦ operatorKernel N hN t a.1.1 a.2)
      (H N hN t) hn hc.measurable hi (fun a x ↦ hk a.1.1 a.1.2 a.2 x)
    filter_upwards [h] with q hq e he c
    exact hq (⟨e, he⟩, c)
  · have hr : 0 ≤ ratio t := div_nonneg ht.1 (by norm_num)
    rw [mul_min_of_nonneg _ _ (mul_nonneg hr hC)]
    apply le_min
    · calc
        _ ≤ ∫ q : T6, (1 / 2 : ℝ) ^ m * periodize (H N hN t) q :=
          integral_mono him (hip.const_mul _) (fun q ↦ mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (norm_relativeTorusDisplacement_le_half q) m) (hp q))
        _ = (1 / 2 : ℝ) ^ m * ∫ q : T6, periodize (H N hN t) q := integral_const_mul _ _
        _ ≤ (1 / 2 : ℝ) ^ m * (ratio t * C) := mul_le_mul_of_nonneg_left hmp (by positivity)
        _ = _ := by ring
    · exact ((integral_relativeMoment_periodize_le _ hn hc.measurable m hm).trans hmom).trans_eq
        (by ring)

/-- The actual channel envelope pays for squared field separation with a
relative second moment. No bound on the Lipschitz cost over time is asserted. -/
theorem exists_uniform_periodic_fieldDifference_bound {F : Type*} [NormedAddCommGroup F] :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M : (N : ℝ) → 0 < N → ℝ → T6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N, ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
        (∀ q, 0 ≤ M N hN t q) ∧ Measurable (M N hN t) ∧ Integrable (M N hN t) ∧
        (∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 → ∀ c : Factor,
          ‖periodicKernel N hN t e c q‖ ≤ M N hN t q) ∧
        (∫ q : T6, M N hN t q) ≤ ratio t * C ∧
        ∀ (L : ℝ≥0) (P : T3 → F), LipschitzWith L P → ∀ x : T3,
          Integrable (fun q ↦
            ‖P (x - firstTorusDisplacement q) - P (x - secondTorusDisplacement q)‖ ^ 2 * M N hN t q) ∧
          (∫ q : T6,
            ‖P (x - firstTorusDisplacement q) - P (x - secondTorusDisplacement q)‖ ^ 2 * M N hN t q) ≤
            ratio t * C * (L : ℝ) ^ 2 * min ((1 / 2 : ℝ) ^ 2) (N⁻¹ ^ 2) := by
  obtain ⟨C, hC, M, hb⟩ := exists_uniform_periodic_envelope 2
  refine ⟨C, hC, M, fun N hN t ht ↦ ?_⟩
  obtain ⟨hn, hm, hi, hmoment, hk, hmass, hbound⟩ := hb N hN t ht
  refine ⟨hn, hm, hi, hk, hmass, fun L P hP x ↦ ?_⟩
  obtain ⟨hdi, hdb⟩ := integrable_and_integral_translated_field_sub_sq_le
    (M N hN t) hn hm hmoment P hP x
  refine ⟨hdi, ?_⟩
  exact (hdb.trans (mul_le_mul_of_nonneg_left hbound (sq_nonneg (L : ℝ)))).trans_eq (by ring)

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentRelativeMoment
