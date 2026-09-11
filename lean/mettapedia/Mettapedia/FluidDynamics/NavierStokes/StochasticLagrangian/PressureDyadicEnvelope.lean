import Mettapedia.Analysis.CompactFourierEnvelope
import Mettapedia.Analysis.DensityLinearChange
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicOperatorKernel

/-!
# Direction-independent envelopes for the exact dyadic pressure kernels

One continuous integrable density dominates all frozen unit directions.
Linear changes retain the Jacobian, the quadratic output-ratio gain, and
the first-moment inverse input scale. No adaptive patch count enters.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope

open MeasureTheory Mettapedia.Analysis.CompactFourierEnvelope
open Mettapedia.Analysis.DensityLinearChange Mettapedia.Analysis.SchwartzLinearChange
open Mettapedia.Analysis.SchwartzDilation Mettapedia.Analysis.SchwartzBilinearKernel
open PressureLowOutputCutoff (ratio)
open PressureLowOutputSymbol (commonSupport isCompact_commonSupport)
open PressureLowOutputKernel (parameterSet isCompact_parameterSet mem_parameterSet)
open PressureDyadicKernel PressureDyadicPhysicalKernel PressureDyadicOperatorKernel
open PressureLowOutputChange PressureLowOutputCoordinates
open scoped SchwartzMap FourierTransform

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

theorem exists_basis_envelope (m : ℕ) :
    ∃ H : E6 → ℝ, (∀ x, 0 ≤ H x) ∧ Continuous H ∧ Integrable H ∧
      Integrable (fun x ↦ ‖x‖ ^ m * H x) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      ∀ i j l : Fin 3, ∀ x, ‖kernel (t, e)
        (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖ ≤ H x := by
  classical
  choose H hn hc hi hm hb using fun a : Fin 3 × Fin 3 × Fin 3 ↦
    exists_uniform_fourierInv_envelope
      (fun p ↦ PressureDyadicSymbol.symbol p (EuclideanSpace.single a.2.1 1)
        (EuclideanSpace.single a.2.2 1) a.1)
      (PressureDyadicSymbol.contDiff_symbol _ _ _) parameterSet isCompact_parameterSet
      commonSupport isCompact_commonSupport (fun p ↦ PressureDyadicSymbol.tsupport_symbol_subset p _ _ _) m
  refine ⟨fun x ↦ ∑ a, H a x, fun x ↦ Finset.sum_nonneg (fun a _ ↦ hn a x),
    continuous_finsetSum _ (fun a _ ↦ hc a), integrable_finsetSum _ (fun a _ ↦ hi a), ?_, ?_⟩
  · simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun a _ ↦ hm a)
  · intro t ht e he i j l x
    exact (hb (i, j, l) (t, e) (mem_parameterSet t ht e he) x).trans
      (Finset.single_le_sum (fun a _ ↦ hn a x) (Finset.mem_univ (i, j, l)))

def physicalEnvelope (H : E6 → ℝ) (t : ℝ) : E6 → ℝ :=
  if h : ratio t = 0 then 0 else
    pullbackDensity (spatialChange (ratio t) h) (fun x ↦ (ratio t) ^ 2 * H x)

def scaledEnvelope (H : E6 → ℝ) (N : ℝ) (hN : 0 < N) (t : ℝ) : E6 → ℝ :=
  pullbackDensity (dilationEquiv N hN.ne') (physicalEnvelope H t)

theorem physicalEnvelope_nonneg (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x) (t : ℝ) (x : E6) :
    0 ≤ physicalEnvelope H t x := by
  unfold physicalEnvelope
  split_ifs
  · rfl
  · exact pullbackDensity_nonneg _ _ (fun y ↦ mul_nonneg (sq_nonneg _) (hH y)) x

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
    (∫ x : E6, physicalEnvelope H t x) = (ratio t) ^ 2 * ∫ x : E6, H x := by
  unfold physicalEnvelope
  split_ifs with hr
  · simp [hr]
  · rw [integral_pullbackDensity, integral_const_mul]

theorem norm_physicalKernel_le (H : E6 → ℝ) (t : ℝ) (e w v : R3) (i : Fin 3)
    (hK : ∀ x, ‖kernel (t, e) w v i x‖ ≤ H x) (x : E6) :
    ‖physicalKernel (t, e) w v i x‖ ≤ physicalEnvelope H t x := by
  by_cases hr : ratio t = 0
  · simp [physicalKernel, physicalEnvelope, hr]
  · simp only [physicalKernel, physicalEnvelope, dif_neg hr, pullback_apply,
      retainedKernel, smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (jacobian_pos _), abs_of_nonneg (sq_nonneg (ratio t)), pullbackDensity]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hK _) (sq_nonneg _))
      (jacobian_pos _).le

theorem norm_scaledKernel_le (H : E6 → ℝ) (N : ℝ) (hN : 0 < N)
    (t : ℝ) (e w v : R3) (i : Fin 3)
    (hK : ∀ x, ‖kernel (t, e) w v i x‖ ≤ H x) (x : E6) :
    ‖scaledKernel N hN (t, e) w v i x‖ ≤ scaledEnvelope H N hN t x := by
  simp only [scaledKernel, dilate, pullback_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (jacobian_pos _), scaledEnvelope, pullbackDensity]
  exact mul_le_mul_of_nonneg_left (norm_physicalKernel_le H t e w v i hK _) (jacobian_pos _).le

theorem integrable_moment_physicalEnvelope (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x)
    (hHc : Continuous H) (m : ℕ) (hHm : Integrable (fun x ↦ ‖x‖ ^ m * H x)) (t : ℝ) :
    Integrable (fun x ↦ ‖x‖ ^ m * physicalEnvelope H t x) := by
  unfold physicalEnvelope
  split_ifs
  · simp
  · apply integrable_moment_pullbackDensity _ _
      (fun x ↦ mul_nonneg (sq_nonneg _) (hH x)) (continuous_const.mul hHc)
    simpa only [mul_left_comm] using hHm.const_mul ((ratio t) ^ 2)

theorem firstMoment_physicalEnvelope_le (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x)
    (hHm : Integrable (fun x ↦ ‖x‖ * H x)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    (∫ x : E6, ‖x‖ * physicalEnvelope H t x) ≤ ratio t * (3 * ∫ x : E6, ‖x‖ * H x) := by
  have hr0 : 0 ≤ ratio t := div_nonneg ht.1 (by norm_num)
  by_cases hr : ratio t = 0
  · simp [physicalEnvelope, hr]
  · have hrp : 0 < ratio t := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hhi : ratio t ≤ 1 := by unfold ratio; linarith [ht.2]
    rw [physicalEnvelope, dif_neg hr]
    have hm : Integrable (fun x : E6 ↦ ‖x‖ ^ 1 * ((ratio t) ^ 2 * H x)) := by
      simpa only [pow_one, mul_left_comm] using hHm.const_mul ((ratio t) ^ 2)
    have h := integral_moment_pullbackDensity_le (spatialChange (ratio t) hr)
      (fun x ↦ (ratio t) ^ 2 * H x) (fun x ↦ mul_nonneg (sq_nonneg _) (hH x)) 1 hm
    simp only [pow_one] at h
    simp_rw [mul_left_comm (‖_‖) ((ratio t) ^ 2)] at h
    rw [integral_const_mul] at h
    calc
      _ ≤ ‖(spatialChange (ratio t) hr).symm.toContinuousLinearMap‖ *
          ((ratio t) ^ 2 * ∫ x : E6, ‖x‖ * H x) := h
      _ ≤ (3 / ratio t) * ((ratio t) ^ 2 * ∫ x : E6, ‖x‖ * H x) :=
        mul_le_mul_of_nonneg_right (opNorm_spatialChange_symm_le _ hrp hhi)
          (mul_nonneg (sq_nonneg _) (integral_nonneg (fun x ↦ mul_nonneg (norm_nonneg _) (hH x))))
      _ = _ := by field_simp

theorem mass_scaledEnvelope (H : E6 → ℝ) (N : ℝ) (hN : 0 < N) (t : ℝ) :
    (∫ x : E6, scaledEnvelope H N hN t x) = (ratio t) ^ 2 * ∫ x : E6, H x := by
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

theorem norm_operatorKernel_le (H : E6 → ℝ) (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3)
    (hK : ∀ i j l : Fin 3, ∀ x, ‖kernel (t, e)
      (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖ ≤ H x) (x : E6) :
    ‖operatorKernel N hN t e x‖ ≤ 27 * scaledEnvelope H N hN t x := by
  apply (norm_assemble_le _ x).trans
  calc
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ∑ _l : Fin 3, scaledEnvelope H N hN t x := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      exact norm_scaledKernel_le H N hN t e _ _ i (hK i j l) x
    _ = _ := by simp; ring

theorem exists_uniform_operator_envelope :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∃ M : (N : ℝ) → 0 < N → ℝ → E6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N, ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
        (∀ x, 0 ≤ M N hN t x) ∧ Continuous (M N hN t) ∧ Integrable (M N hN t) ∧
        Integrable (fun x ↦ ‖x‖ * M N hN t x) ∧
        (∀ e : R3, ‖e‖ = 1 → ∀ x, ‖operatorKernel N hN t e x‖ ≤ M N hN t x) ∧
        (∫ x : E6, M N hN t x) ≤ (ratio t) ^ 2 * C0 ∧
        (∫ x : E6, ‖x‖ * M N hN t x) ≤ (ratio t / N) * C1 := by
  obtain ⟨H, hn, hc, hi, hm, hb⟩ := exists_basis_envelope 1
  simp only [pow_one] at hm
  have hmass : (0 : ℝ) ≤ ∫ x : E6, H x := MeasureTheory.integral_nonneg hn
  have hmom : (0 : ℝ) ≤ ∫ x : E6, ‖x‖ * H x :=
    MeasureTheory.integral_nonneg (fun x ↦ mul_nonneg (norm_nonneg x) (hn x))
  refine ⟨27 * ∫ x : E6, H x, 81 * ∫ x : E6, ‖x‖ * H x,
    mul_nonneg (by norm_num) hmass, mul_nonneg (by norm_num) hmom,
    fun N hN t x ↦ 27 * scaledEnvelope H N hN t x, ?_⟩
  intro N hN t ht
  have hp := physicalEnvelope_nonneg H hn t
  have hpc := continuous_physicalEnvelope H hc t
  have hpi := integrable_physicalEnvelope H hi t
  have hpm := integrable_moment_physicalEnvelope H hn hc 1 (by simpa using hm) t
  have hsm := integrable_moment_pullbackDensity (dilationEquiv (E := E6) N hN.ne')
    (physicalEnvelope H t) hp hpc 1 hpm
  refine ⟨fun x ↦ mul_nonneg (by norm_num) (pullbackDensity_nonneg _ _ hp x),
    continuous_const.mul (continuous_pullbackDensity _ _ hpc),
    (integrable_pullbackDensity _ _ hpi).const_mul 27, ?_,
    fun e he x ↦ norm_operatorKernel_le H N hN t e (hb t ht e he) x, ?_, ?_⟩
  · simpa only [pow_one, mul_left_comm, scaledEnvelope] using hsm.const_mul 27
  · rw [integral_const_mul, mass_scaledEnvelope]
    exact le_of_eq (by ring)
  · simp_rw [mul_left_comm (‖_‖) (27 : ℝ)]
    rw [integral_const_mul, firstMoment_scaledEnvelope]
    calc
      _ ≤ 27 * (N⁻¹ * (ratio t * (3 * ∫ x : E6, ‖x‖ * H x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (firstMoment_physicalEnvelope_le H hn hm t ht) (inv_nonneg.mpr hN.le)) (by norm_num)
      _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope
