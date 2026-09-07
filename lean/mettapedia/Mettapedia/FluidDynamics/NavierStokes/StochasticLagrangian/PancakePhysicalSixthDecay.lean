import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeContinuousCoordinateJet
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLatticeDecayEnvelope

/-!
# Sixth-order decay from actual continuous coordinate derivatives

The continuous field and its pure sixth coordinate derivatives control
the sixth weighted coefficient uniformly. The constants are deliberately
explicit. This converts spatial regularity to a Fourier envelope without
assuming a symbol identity or a coefficient-decay bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalSixthDecay

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicComplexStretch PancakeCurlOutputTail PancakePhysicalFourierDerivative
open PancakeContinuousCoordinateJet PancakeLatticeDecayEnvelope PancakeArbitraryDataBlocks

local notation "T3" => UnitAddTorus (Fin 3)

theorem norm_coefficientVec_le_three (v : VelocityCoefficient) (B : ℝ) (hB : 0 ≤ B)
    (hv : ∀ i, ‖v i‖ ≤ B) : ‖coefficientVec v‖ ≤ 3 * B := by
  have hs : ‖coefficientVec v‖ ^ 2 ≤ 3 * B ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ : Fin 3, B ^ 2 := Finset.sum_le_sum (fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hv i) 2)
      _ = _ := by simp
  nlinarith [norm_nonneg (coefficientVec v), sq_nonneg B]

theorem exists_frequency_coordinate_dominates (k : Wavevector) :
    ∃ j : Fin 3, ‖frequencyVec k‖ ≤ 3 * ‖(k j : ℂ)‖ := by
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun j : Fin 3 ↦ ‖(k j : ℂ)‖) Finset.univ_nonempty
  refine ⟨j, ?_⟩
  exact norm_coefficientVec_le_three (wavevectorCoefficient k) _ (norm_nonneg _) (fun i ↦ hj i (Finset.mem_univ i))

theorem scalar_sixthMoment_le (f : T3 → ℂ) (hf : HasContinuousCoordinateJet 6 f)
    (B : ℝ)
    (hfB : ‖(⟨f, by simpa only [coordinateJet_zero] using hf.1 0 0 (by omega)⟩ : C(T3, ℂ))‖ ≤ B)
    (hdB : ∀ j, ‖(⟨coordinateJet f j 6, hf.1 j 6 le_rfl⟩ : C(T3, ℂ))‖ ≤ B)
    (k : Wavevector) :
    (1 + ‖frequencyVec k‖) ^ 6 * ‖UnitAddTorus.mFourierCoeff f k‖ ≤ 4096 * B := by
  obtain ⟨j, hj⟩ := exists_frequency_coordinate_dominates k
  have hP : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  by_cases hq : 1 ≤ ‖(k j : ℂ)‖
  · have hscale : 1 + ‖frequencyVec k‖ ≤ 4 * ((2 * Real.pi) * ‖(k j : ℂ)‖) := by
      nlinarith [mul_le_mul_of_nonneg_right hP (norm_nonneg (k j : ℂ))]
    calc
      _ ≤ (4 * ((2 * Real.pi) * ‖(k j : ℂ)‖)) ^ 6 * ‖UnitAddTorus.mFourierCoeff f k‖ := by gcongr
      _ = 4096 * (((2 * Real.pi) * ‖(k j : ℂ)‖) ^ 6 * ‖UnitAddTorus.mFourierCoeff f k‖) := by ring
      _ ≤ 4096 * B := mul_le_mul_of_nonneg_left
        ((coordinateJet_frequency_bound f 6 hf j 6 le_rfl k).trans (hdB j)) (by norm_num)
  · have hscale : 1 + ‖frequencyVec k‖ ≤ 4 := by linarith [not_le.mp hq]
    have hcoeff := (norm_fourierCoeff_le
      (⟨f, by simpa only [coordinateJet_zero] using hf.1 0 0 (by omega)⟩ : C(T3, ℂ)) k).trans hfB
    change ‖UnitAddTorus.mFourierCoeff f k‖ ≤ B at hcoeff
    calc
      _ ≤ (4 : ℝ) ^ 6 * B := by gcongr
      _ = _ := by norm_num

theorem vector_sixthMoment_le (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 6 (fun x ↦ f x i)) (B : ℝ) (hB : 0 ≤ B)
    (hfB : ∀ i, ‖(⟨fun x ↦ f x i, by simpa only [coordinateJet_zero] using (hf i).1 0 0 (by omega)⟩ : C(T3, ℂ))‖ ≤ B)
    (hdB : ∀ i j, ‖(⟨coordinateJet (fun x ↦ f x i) j 6, (hf i).1 j 6 le_rfl⟩ : C(T3, ℂ))‖ ≤ B)
    (k : Wavevector) : fourierMoment 6 (torusFourierVelocity f) k ≤ 12288 * B := by
  have hcoord := fun i ↦ scalar_sixthMoment_le (fun x ↦ f x i) (hf i) B (hfB i) (hdB i) k
  have h := norm_coefficientVec_le_three
    (((1 + ‖frequencyVec k‖)^6 : ℝ) • torusFourierVelocity f k) (4096 * B) (by positivity)
    (fun i ↦ by simpa only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, torusFourierVelocity,
      abs_of_nonneg (by positivity : 0 ≤ (1 + ‖frequencyVec k‖)^6)] using hcoord i)
  change ‖((1 + ‖frequencyVec k‖)^6 : ℝ) • coefficientVec (torusFourierVelocity f k)‖ ≤ _ at h
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 + ‖frequencyVec k‖)^6)] at h
  calc
    _ ≤ 3 * (4096 * B) := h
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalSixthDecay
