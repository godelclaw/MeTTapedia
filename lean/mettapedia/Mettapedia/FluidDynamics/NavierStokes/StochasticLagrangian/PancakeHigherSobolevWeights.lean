import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSobolevWeights

/-!
# Polynomial Sobolev weights of arbitrary integer order

The lattice sum from order two controls every higher inverse-square weight.
A polynomial splitting factor pays the finite convolution without a cutoff
or mode-count constant.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeHigherSobolevWeights

open scoped BigOperators
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator
open PancakeFiniteConvolutionL2 PancakeSobolevWeights PancakeCurlOutputTail

def orderWeight (m : ℕ) (k : Wavevector) : ℝ := (1 + ‖frequencyVec k‖)^m

theorem orderWeight_pos (m : ℕ) (k : Wavevector) : 0 < orderWeight m k := by
  unfold orderWeight
  positivity

theorem orderWeight_lower (m : ℕ) (hm : 2 ≤ m) (k : Wavevector) :
    weight k ≤ orderWeight m k :=
  pow_le_pow_right₀ (by linarith [norm_nonneg (frequencyVec k)]) hm

theorem orderWeight_add_le (m : ℕ) (k l : Wavevector) :
    orderWeight m (k+l) ≤ (2 : ℝ)^m * (orderWeight m k + orderWeight m l) := by
  have hn : ‖frequencyVec (k+l)‖ ≤ ‖frequencyVec k‖ + ‖frequencyVec l‖ := by
    rw [frequencyVec_add]
    exact norm_add_le _ _
  rcases le_total ‖frequencyVec k‖ ‖frequencyVec l‖ with h | h
  · have hs : 1 + ‖frequencyVec (k+l)‖ ≤ 2 * (1 + ‖frequencyVec l‖) := by linarith
    calc
      _ ≤ (2 * (1 + ‖frequencyVec l‖))^m := pow_le_pow_left₀ (by positivity) hs m
      _ = (2 : ℝ)^m * orderWeight m l := by rw [mul_pow]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (orderWeight_pos m k).le) (by positivity)
  · have hs : 1 + ‖frequencyVec (k+l)‖ ≤ 2 * (1 + ‖frequencyVec k‖) := by linarith
    calc
      _ ≤ (2 * (1 + ‖frequencyVec k‖))^m := pow_le_pow_left₀ (by positivity) hs m
      _ = (2 : ℝ)^m * orderWeight m k := by rw [mul_pow]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (orderWeight_pos m l).le) (by positivity)

theorem sum_inverse_orderWeight_sq_le (m : ℕ) (hm : 2 ≤ m) (M : Finset Wavevector) :
    (∑ k ∈ M, (1 / orderWeight m k)^2) ≤ latticeMass := by
  apply le_trans _ (sum_inverse_weight_sq_le M)
  apply Finset.sum_le_sum
  intro k hk
  exact pow_le_pow_left₀ (div_nonneg zero_le_one (orderWeight_pos m k).le)
    (one_div_le_one_div_of_le (weight_pos k) (orderWeight_lower m hm k)) 2

theorem sum_le_orderL2 (m : ℕ) (hm : 2 ≤ m) (M : Finset Wavevector) (a : Wavevector → ℝ) :
    (∑ k ∈ M, a k) ≤ Real.sqrt latticeMass * sizeL2 M (fun k ↦ orderWeight m k * a k) := by
  have he (k : Wavevector) : a k = (1 / orderWeight m k) * (orderWeight m k * a k) := by
    field_simp [(orderWeight_pos m k).ne']
  calc
    _ = ∑ k ∈ M, (1 / orderWeight m k) * (orderWeight m k * a k) :=
      Finset.sum_congr rfl (fun k _ ↦ he k)
    _ ≤ _ := (Real.sum_mul_le_sqrt_mul_sqrt M (fun k ↦ 1 / orderWeight m k)
      (fun k ↦ orderWeight m k * a k)).trans
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (sum_inverse_orderWeight_sq_le m hm M))
          (sizeL2_nonneg _ _))

def orderEnergy (m : ℕ) (M : Finset Wavevector) (a : Wavevector → ℝ) : ℝ :=
  ∑ k ∈ M, (orderWeight m k * a k)^2

def orderDissipation (m : ℕ) (M : Finset Wavevector) (a : Wavevector → ℝ) : ℝ :=
  orderEnergy m M (fun k ↦ ‖frequencyVec k‖ * a k)

theorem orderEnergy_nonneg (m : ℕ) (M : Finset Wavevector) (a : Wavevector → ℝ) :
    0 ≤ orderEnergy m M a := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem orderDissipation_nonneg (m : ℕ) (M : Finset Wavevector) (a : Wavevector → ℝ) :
    0 ≤ orderDissipation m M a := orderEnergy_nonneg m M _

def orderTriad (m : ℕ) (M : Finset Wavevector) (a : Wavevector → ℝ) : ℝ :=
  ∑ k ∈ M, ∑ l ∈ M,
    cut M (fun q ↦ orderWeight m q ^ 2 * a q) (k+l) * a k * (‖frequencyVec l‖ * a l)

theorem orderTriad_split (m : ℕ) (M : Finset Wavevector) (a : Wavevector → ℝ)
    (ha : ∀ k, 0 ≤ a k) :
    orderTriad m M a ≤ (2 : ℝ)^m *
      (triadSum M (fun q ↦ orderWeight m q * a q) (fun k ↦ orderWeight m k * a k)
          (fun l ↦ ‖frequencyVec l‖ * a l) +
       triadSum M (fun q ↦ orderWeight m q * a q) a
          (fun l ↦ orderWeight m l * (‖frequencyVec l‖ * a l))) := by
  unfold orderTriad triadSum
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  by_cases hq : k+l ∈ M
  · simp only [cut, if_pos hq]
    have h := mul_le_mul_of_nonneg_right (orderWeight_add_le m k l)
      (mul_nonneg (mul_nonneg (mul_nonneg (orderWeight_pos m (k+l)).le (ha (k+l))) (ha k))
        (mul_nonneg (norm_nonneg (frequencyVec l)) (ha l)))
    nlinarith
  · simp [cut, hq]

theorem orderTriad_le (m : ℕ) (hm : 2 ≤ m) (M : Finset Wavevector) (a : Wavevector → ℝ)
    (ha : ∀ k, 0 ≤ a k) :
    orderTriad m M a ≤ 2 * (2 : ℝ)^m * Real.sqrt latticeMass *
      orderEnergy m M a * Real.sqrt (orderDissipation m M a) := by
  let b := fun k ↦ orderWeight m k * a k
  let c := fun k ↦ ‖frequencyVec k‖ * a k
  have hc : ∀ k, 0 ≤ c k := fun k ↦ mul_nonneg (norm_nonneg _) (ha k)
  have he : sizeL2 M b ^ 2 = orderEnergy m M a := Real.sq_sqrt (orderEnergy_nonneg m M a)
  have hD : sizeL2 M (fun k ↦ orderWeight m k * c k) =
      Real.sqrt (orderDissipation m M a) := rfl
  have h1 := (triadSum_le_rightL1 M b b c (fun k _ ↦ hc k)).trans
    (mul_le_mul_of_nonneg_left (sum_le_orderL2 m hm M c)
      (mul_nonneg (sizeL2_nonneg M b) (sizeL2_nonneg M b)))
  have h2 := (triadSum_le_leftL1 M b a (fun k ↦ orderWeight m k * c k) (fun k _ ↦ ha k)).trans
    (mul_le_mul_of_nonneg_left (sum_le_orderL2 m hm M a)
      (mul_nonneg (sizeL2_nonneg M b) (sizeL2_nonneg M (fun k ↦ orderWeight m k * c k))))
  have h1' : triadSum M b b c ≤
      Real.sqrt latticeMass * orderEnergy m M a * Real.sqrt (orderDissipation m M a) := by
    calc
      _ ≤ _ := h1
      _ = _ := by rw [← he, hD]; ring
  have h2' : triadSum M b a (fun k ↦ orderWeight m k * c k) ≤
      Real.sqrt latticeMass * orderEnergy m M a * Real.sqrt (orderDissipation m M a) := by
    calc
      _ ≤ _ := h2
      _ = _ := by rw [← he, hD]; ring
  have hs := orderTriad_split m M a ha
  change orderTriad m M a ≤ (2 : ℝ)^m *
    (triadSum M b b c + triadSum M b a (fun k ↦ orderWeight m k * c k)) at hs
  calc
    _ ≤ _ := hs.trans (mul_le_mul_of_nonneg_left (add_le_add h1' h2') (by positivity))
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PancakeHigherSobolevWeights
