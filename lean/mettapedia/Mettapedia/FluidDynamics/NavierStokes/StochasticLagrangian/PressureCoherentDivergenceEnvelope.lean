import Mettapedia.Analysis.DensityLinearChange
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergenceOperatorKernel

/-!
# One envelope for all coherent bilinear pressure channels

The same nonnegative density dominates every unit direction and every
input-frequency channel. Its mass retains one output/input ratio, while
its first spatial moment retains the inverse input scale. Constants are
chosen before the scale, ratio, direction, or channel.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceEnvelope

open MeasureTheory Mettapedia.Analysis.DensityLinearChange
open Mettapedia.Analysis.SchwartzLinearChange Mettapedia.Analysis.SchwartzDilation
open PressureLowOutputCutoff (ratio)
open PressureLowOutputChange
open PressureCoherentDivergenceChannel (Factor kernel)
open PressureCoherentDivergenceChannelKernel
open PressureCoherentDivergenceOperatorKernel (operatorKernel)
open scoped SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

def physicalEnvelope (H : E6 → ℝ) (t : ℝ) : E6 → ℝ :=
  if h : ratio t = 0 then 0 else
    pullbackDensity (spatialChange (ratio t) h) (fun x ↦ |ratio t| * H x)

def scaledEnvelope (H : E6 → ℝ) (N : ℝ) (hN : 0 < N) (t : ℝ) : E6 → ℝ :=
  pullbackDensity (dilationEquiv N hN.ne') (physicalEnvelope H t)

theorem physicalEnvelope_nonneg (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x) (t : ℝ) (x : E6) :
    0 ≤ physicalEnvelope H t x := by
  unfold physicalEnvelope
  split_ifs
  · rfl
  · exact pullbackDensity_nonneg _ _ (fun y ↦ mul_nonneg (abs_nonneg _) (hH y)) x

theorem continuous_physicalEnvelope (H : E6 → ℝ) (hH : Continuous H) (t : ℝ) :
    Continuous (physicalEnvelope H t) := by
  unfold physicalEnvelope
  split_ifs
  · exact continuous_const
  · exact continuous_pullbackDensity _ _ (continuous_const.mul hH)

theorem integrable_physicalEnvelope (H : E6 → ℝ) (hH : Integrable H) (t : ℝ) :
    Integrable (physicalEnvelope H t) := by
  unfold physicalEnvelope
  split_ifs
  · exact integrable_zero _ _ _
  · exact integrable_pullbackDensity _ _ (hH.const_mul _)

theorem mass_physicalEnvelope (H : E6 → ℝ) (t : ℝ) :
    (∫ x : E6, physicalEnvelope H t x) = |ratio t| * ∫ x : E6, H x := by
  unfold physicalEnvelope
  split_ifs with hr
  · simp [hr]
  · rw [integral_pullbackDensity, integral_const_mul]

theorem norm_physicalKernel_le (H : E6 → ℝ) (t : ℝ) (e : R3) (c : Factor) (i : Fin 3)
    (hK : ∀ x, ‖kernel (t, e) c i x‖ ≤ H x) (x : E6) :
    ‖physicalKernel (t, e) c i x‖ ≤ physicalEnvelope H t x := by
  by_cases hr : ratio t = 0
  · simp [physicalKernel, physicalEnvelope, hr]
  · simp only [physicalKernel, physicalEnvelope, dif_neg hr, pullback_apply,
      retainedKernel, smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (jacobian_pos _), pullbackDensity]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hK _) (abs_nonneg _))
      (jacobian_pos _).le

theorem norm_scaledKernel_le (H : E6 → ℝ) (N : ℝ) (hN : 0 < N)
    (t : ℝ) (e : R3) (c : Factor) (i : Fin 3)
    (hK : ∀ x, ‖kernel (t, e) c i x‖ ≤ H x) (x : E6) :
    ‖scaledKernel N hN (t, e) c i x‖ ≤ scaledEnvelope H N hN t x := by
  simp only [scaledKernel, dilate, pullback_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (jacobian_pos _), scaledEnvelope, pullbackDensity]
  exact mul_le_mul_of_nonneg_left (norm_physicalKernel_le H t e c i hK _) (jacobian_pos _).le

theorem integrable_moment_physicalEnvelope (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x)
    (hHc : Continuous H) (m : ℕ) (hHm : Integrable (fun x ↦ ‖x‖ ^ m * H x)) (t : ℝ) :
    Integrable (fun x ↦ ‖x‖ ^ m * physicalEnvelope H t x) := by
  unfold physicalEnvelope
  split_ifs
  · simp
  · apply integrable_moment_pullbackDensity _ _
      (fun x ↦ mul_nonneg (abs_nonneg _) (hH x)) (continuous_const.mul hHc)
    simpa only [mul_left_comm] using hHm.const_mul |ratio t|

theorem firstMoment_physicalEnvelope_le (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x)
    (hHm : Integrable (fun x ↦ ‖x‖ * H x)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    (∫ x : E6, ‖x‖ * physicalEnvelope H t x) ≤ 3 * ∫ x : E6, ‖x‖ * H x := by
  have hr0 : 0 ≤ ratio t := div_nonneg ht.1 (by norm_num)
  by_cases hr : ratio t = 0
  · simp only [physicalEnvelope, hr, dif_pos, Pi.zero_apply, mul_zero, integral_zero]
    exact mul_nonneg (by norm_num) (integral_nonneg (fun x ↦ mul_nonneg (norm_nonneg _) (hH x)))
  · have hrp : 0 < ratio t := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hhi : ratio t ≤ 1 := by unfold ratio; linarith [ht.2]
    rw [physicalEnvelope, dif_neg hr]
    have hm : Integrable (fun x : E6 ↦ ‖x‖ ^ 1 * (|ratio t| * H x)) := by
      simpa only [pow_one, mul_left_comm] using hHm.const_mul |ratio t|
    have h := integral_moment_pullbackDensity_le (spatialChange (ratio t) hr)
      (fun x ↦ |ratio t| * H x) (fun x ↦ mul_nonneg (abs_nonneg _) (hH x)) 1 hm
    simp only [pow_one, abs_of_nonneg hr0] at h
    simp_rw [mul_left_comm (‖_‖) (ratio t)] at h
    rw [integral_const_mul] at h
    calc
      _ ≤ ‖(spatialChange (ratio t) hr).symm.toContinuousLinearMap‖ *
          (ratio t * ∫ x : E6, ‖x‖ * H x) := by simpa only [abs_of_nonneg hr0] using h
      _ ≤ (3 / ratio t) * (ratio t * ∫ x : E6, ‖x‖ * H x) :=
        mul_le_mul_of_nonneg_right (opNorm_spatialChange_symm_le _ hrp hhi)
          (mul_nonneg hr0 (integral_nonneg (fun x ↦ mul_nonneg (norm_nonneg _) (hH x))))
      _ = _ := by field_simp

theorem mass_scaledEnvelope (H : E6 → ℝ) (N : ℝ) (hN : 0 < N) (t : ℝ) :
    (∫ x : E6, scaledEnvelope H N hN t x) = |ratio t| * ∫ x : E6, H x := by
  rw [scaledEnvelope, integral_pullbackDensity, mass_physicalEnvelope]

theorem firstMoment_scaledEnvelope (H : E6 → ℝ) (N : ℝ) (hN : 0 < N) (t : ℝ) :
    (∫ x : E6, ‖x‖ * scaledEnvelope H N hN t x) =
      N⁻¹ * ∫ x : E6, ‖x‖ * physicalEnvelope H t x := by
  have h := integral_moment_pullbackDensity (dilationEquiv (E := E6) N hN.ne')
    (physicalEnvelope H t) 1
  simp only [pow_one, dilationEquiv_symm_apply, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hN] at h
  rw [scaledEnvelope, h]
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup

theorem exists_uniform_operator_envelope :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∃ M : (N : ℝ) → 0 < N → ℝ → E6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N, ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
        (∀ x, 0 ≤ M N hN t x) ∧ Continuous (M N hN t) ∧ Integrable (M N hN t) ∧
        Integrable (fun x ↦ ‖x‖ * M N hN t x) ∧
        (∀ e : R3, ‖e‖ = 1 → ∀ c : Factor, ∀ x,
          ‖operatorKernel N hN t e c x‖ ≤ M N hN t x) ∧
        (∫ x : E6, M N hN t x) ≤ ratio t * C0 ∧
        (∫ x : E6, ‖x‖ * M N hN t x) ≤ C1 / N := by
  obtain ⟨H, hn, hc, hi, hm, hb⟩ := PressureCoherentDivergenceChannel.exists_uniform_envelope 1
  simp only [pow_one] at hm
  have hmass : (0 : ℝ) ≤ ∫ x : E6, H x := integral_nonneg hn
  have hmom : (0 : ℝ) ≤ ∫ x : E6, ‖x‖ * H x :=
    integral_nonneg (fun x ↦ mul_nonneg (norm_nonneg x) (hn x))
  refine ⟨3 * ∫ x : E6, H x, 9 * ∫ x : E6, ‖x‖ * H x,
    mul_nonneg (by norm_num) hmass, mul_nonneg (by norm_num) hmom,
    fun N hN t x ↦ 3 * scaledEnvelope H N hN t x, ?_⟩
  intro N hN t ht
  have hp := physicalEnvelope_nonneg H hn t
  have hpc := continuous_physicalEnvelope H hc t
  have hpi := integrable_physicalEnvelope H hi t
  have hpm := integrable_moment_physicalEnvelope H hn hc 1 (by simpa using hm) t
  have hsm := integrable_moment_pullbackDensity (dilationEquiv (E := E6) N hN.ne')
    (physicalEnvelope H t) hp hpc 1 hpm
  refine ⟨fun x ↦ mul_nonneg (by norm_num) (pullbackDensity_nonneg _ _ hp x),
    continuous_const.mul (continuous_pullbackDensity _ _ hpc),
    (integrable_pullbackDensity _ _ hpi).const_mul 3, ?_, ?_, ?_, ?_⟩
  · simpa only [pow_one, mul_left_comm, scaledEnvelope] using hsm.const_mul 3
  · intro e he c x
    exact PressureCoherentDivergenceOperatorKernel.norm_operatorKernel_le N hN t e he c
      (scaledEnvelope H N hN t) (fun i ↦ norm_scaledKernel_le H N hN t e c i (hb t ht e he c i)) x
  · rw [integral_const_mul, mass_scaledEnvelope,
      abs_of_nonneg (show 0 ≤ ratio t from div_nonneg ht.1 (by norm_num))]
    exact le_of_eq (by ring)
  · simp_rw [mul_left_comm (‖_‖) (3 : ℝ)]
    rw [integral_const_mul, firstMoment_scaledEnvelope]
    calc
      _ ≤ 3 * (N⁻¹ * (3 * ∫ x : E6, ‖x‖ * H x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (firstMoment_physicalEnvelope_le H hn hm t ht) (inv_nonneg.mpr hN.le)) (by norm_num)
      _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceEnvelope
