import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherSobolevVelocityRate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCompactJetEnvelope

/-!
# Higher Sobolev initial bounds from actual coordinate derivatives

An order-N coordinate jet gives an explicit order-N Fourier moment bound.
Taking N=m+2 makes the squared order-m coefficients bounded by the same
summable inverse-fourth-power lattice weight.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeHigherInitialEnergy

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicComplexStretch PancakeCurlOutputTail PancakePhysicalFourierDerivative
open PancakeContinuousCoordinateJet PancakeLatticeDecayEnvelope PancakeArbitraryDataBlocks
open PancakePhysicalSixthDecay PancakeCompactJetEnvelope PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeSobolevVelocityRate PancakeSobolevWeights

local notation "T3" => UnitAddTorus (Fin 3)

theorem scalar_orderMoment_le (N : ℕ) (f : T3 → ℂ) (hf : HasContinuousCoordinateJet N f)
    (B : ℝ)
    (hfB : ‖(⟨f, by simpa only [coordinateJet_zero] using hf.1 0 0 (by omega)⟩ : C(T3, ℂ))‖ ≤ B)
    (hdB : ∀ j, ‖(⟨coordinateJet f j N, hf.1 j N le_rfl⟩ : C(T3, ℂ))‖ ≤ B)
    (k : Wavevector) :
    (1 + ‖frequencyVec k‖)^N * ‖UnitAddTorus.mFourierCoeff f k‖ ≤ (4 : ℝ)^N * B := by
  obtain ⟨j, hj⟩ := exists_frequency_coordinate_dominates k
  have hP : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  by_cases hq : 1 ≤ ‖(k j : ℂ)‖
  · have hscale : 1 + ‖frequencyVec k‖ ≤ 4 * ((2 * Real.pi) * ‖(k j : ℂ)‖) := by
      nlinarith [mul_le_mul_of_nonneg_right hP (norm_nonneg (k j : ℂ))]
    calc
      _ ≤ (4 * ((2 * Real.pi) * ‖(k j : ℂ)‖))^N * ‖UnitAddTorus.mFourierCoeff f k‖ := by gcongr
      _ = (4 : ℝ)^N * (((2 * Real.pi) * ‖(k j : ℂ)‖)^N *
          ‖UnitAddTorus.mFourierCoeff f k‖) := by rw [mul_pow]; ring
      _ ≤ (4 : ℝ)^N * B := mul_le_mul_of_nonneg_left
        ((coordinateJet_frequency_bound f N hf j N le_rfl k).trans (hdB j)) (by positivity)
  · have hscale : 1 + ‖frequencyVec k‖ ≤ 4 := by linarith [not_le.mp hq]
    have hcoeff := (norm_fourierCoeff_le
      (⟨f, by simpa only [coordinateJet_zero] using hf.1 0 0 (by omega)⟩ : C(T3, ℂ)) k).trans hfB
    change ‖UnitAddTorus.mFourierCoeff f k‖ ≤ B at hcoeff
    gcongr

theorem vector_orderMoment_le (N : ℕ) (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet N (fun x ↦ f x i)) (B : ℝ) (hB : 0 ≤ B)
    (hfB : ∀ i, ‖(⟨fun x ↦ f x i,
      by simpa only [coordinateJet_zero] using (hf i).1 0 0 (by omega)⟩ : C(T3, ℂ))‖ ≤ B)
    (hdB : ∀ i j, ‖(⟨coordinateJet (fun x ↦ f x i) j N,
      (hf i).1 j N le_rfl⟩ : C(T3, ℂ))‖ ≤ B)
    (k : Wavevector) : fourierMoment N (torusFourierVelocity f) k ≤ 3 * (4 : ℝ)^N * B := by
  have hcoord := fun i ↦ scalar_orderMoment_le N (fun x ↦ f x i) (hf i) B (hfB i) (hdB i) k
  have h := norm_coefficientVec_le_three
    (((1 + ‖frequencyVec k‖)^N : ℝ) • torusFourierVelocity f k) ((4 : ℝ)^N * B) (by positivity)
    (fun i ↦ by simpa only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, torusFourierVelocity,
      abs_of_nonneg (by positivity : 0 ≤ (1 + ‖frequencyVec k‖)^N)] using hcoord i)
  change ‖((1 + ‖frequencyVec k‖)^N : ℝ) • coefficientVec (torusFourierVelocity f k)‖ ≤ _ at h
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 + ‖frequencyVec k‖)^N)] at h
  calc
    _ ≤ 3 * ((4 : ℝ)^N * B) := h
    _ = _ := by ring

theorem exists_physical_orderMoment_bound (N : ℕ) (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet N (fun x ↦ f x i)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k, fourierMoment N (torusFourierVelocity f) k ≤ A := by
  have hc (i : Fin 3) : Continuous (fun x ↦ f x i) := (hf i).1 0 0 (by omega)
  obtain ⟨B0, hB0, hb0⟩ := exists_finite_continuous_family_bound _ hc
  obtain ⟨BN, hBN, hbN⟩ := exists_finite_continuous_family_bound
    (fun ij : Fin 3 × Fin 3 ↦ coordinateJet (fun x ↦ f x ij.1) ij.2 N)
    (fun ij ↦ (hf ij.1).1 ij.2 N le_rfl)
  refine ⟨3 * (4 : ℝ)^N * (B0+BN), by positivity, fun k ↦ ?_⟩
  apply vector_orderMoment_le N f hf (B0+BN) (by positivity)
  · intro i
    apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ B0+BN)).mpr
    intro x
    exact (hb0 i x).trans (le_add_of_nonneg_right hBN)
  · intro i j
    apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ B0+BN)).mpr
    intro x
    exact (hbN (i,j) x).trans (le_add_of_nonneg_left hB0)

theorem orderEnergy_le_moment_bound (m : ℕ) (M : Finset Wavevector) (u : FourierVelocity)
    (A : ℝ) (hA : ∀ k, fourierMoment (m+2) u k ≤ A) :
    velocityEnergy m M u ≤ A^2 * latticeMass := by
  have hp (k : Wavevector) :
      orderWeight m k * amplitude u k ≤ A / (1 + ‖frequencyVec k‖)^2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h := hA k
    change (1 + ‖frequencyVec k‖)^(m+2) * amplitude u k ≤ A at h
    simpa only [orderWeight, pow_add, mul_assoc, mul_comm, mul_left_comm] using h
  have hs (k : Wavevector) :
      (orderWeight m k * amplitude u k)^2 ≤ A^2 * latticeDecayWeight k := by
    calc
      _ ≤ (A / (1 + ‖frequencyVec k‖)^2)^2 :=
        pow_le_pow_left₀ (mul_nonneg (orderWeight_pos m k).le (norm_nonneg _)) (hp k) 2
      _ = _ := by simp [div_pow, latticeDecayWeight, ← pow_mul]; ring
  change (∑ k ∈ M, (orderWeight m k * amplitude u k)^2) ≤ _
  calc
    _ ≤ ∑ k ∈ M, A^2 * latticeDecayWeight k := Finset.sum_le_sum (fun k _ ↦ hs k)
    _ = A^2 * ∑ k ∈ M, latticeDecayWeight k := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (summable_latticeDecayWeight.sum_le_tsum M (fun k _ ↦ (latticeDecayWeight_pos k).le))
      (sq_nonneg A)

theorem exists_physical_orderEnergy_bound (m : ℕ) (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet (m+2) (fun x ↦ f x i)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : Finset Wavevector, velocityEnergy m M (torusFourierVelocity f) ≤ B := by
  obtain ⟨A, hA, ha⟩ := exists_physical_orderMoment_bound (m+2) f hf
  exact ⟨A^2 * latticeMass, mul_nonneg (sq_nonneg A) latticeMass_nonneg,
    fun M ↦ orderEnergy_le_moment_bound m M _ A ha⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeHigherInitialEnergy
