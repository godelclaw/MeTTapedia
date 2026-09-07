import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFiniteConvolutionL2

/-!
# Uniform second-order Fourier weights

The fixed three-dimensional inverse-fourth-power lattice sum pays the
l1 factors in the finite convolution estimate. No adaptive cardinality
or cutoff radius enters the constant.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSobolevWeights

open scoped BigOperators
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLatticeDecayEnvelope PancakeFiniteConvolutionL2

def weight (k : Wavevector) : ℝ := (1 + ‖frequencyVec k‖) ^ 2
def latticeMass : ℝ := ∑' k : Wavevector, latticeDecayWeight k

theorem weight_pos (k : Wavevector) : 0 < weight k := by unfold weight; positivity

theorem latticeMass_nonneg : 0 ≤ latticeMass :=
  tsum_nonneg (fun k ↦ (latticeDecayWeight_pos k).le)

theorem weight_add_le (k l : Wavevector) : weight (k + l) ≤ 2 * (weight k + weight l) := by
  have hn : ‖frequencyVec (k + l)‖ ≤ ‖frequencyVec k‖ + ‖frequencyVec l‖ := by
    rw [frequencyVec_add]
    exact norm_add_le _ _
  have hh : (1 + ‖frequencyVec (k + l)‖)^2 ≤
      (1 + ‖frequencyVec k‖ + ‖frequencyVec l‖)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  unfold weight
  nlinarith [sq_nonneg (‖frequencyVec k‖ - ‖frequencyVec l‖),
    norm_nonneg (frequencyVec k), norm_nonneg (frequencyVec l)]

theorem sum_inverse_weight_sq_le (M : Finset Wavevector) :
    (∑ k ∈ M, (1 / weight k)^2) ≤ latticeMass := by
  have he (k : Wavevector) : (1 / weight k)^2 = latticeDecayWeight k := by
    simp [weight, latticeDecayWeight]
    ring
  simp_rw [he]
  exact summable_latticeDecayWeight.sum_le_tsum M
    (fun k _ ↦ (latticeDecayWeight_pos k).le)

theorem sum_le_weightedL2 (M : Finset Wavevector) (a : Wavevector → ℝ) :
    (∑ k ∈ M, a k) ≤ Real.sqrt latticeMass * sizeL2 M (fun k ↦ weight k * a k) := by
  have he (k : Wavevector) : a k = (1 / weight k) * (weight k * a k) := by
    field_simp [(weight_pos k).ne']
  calc
    _ = ∑ k ∈ M, (1 / weight k) * (weight k * a k) := Finset.sum_congr rfl (fun k _ ↦ he k)
    _ ≤ _ := (Real.sum_mul_le_sqrt_mul_sqrt M (fun k ↦ 1 / weight k)
      (fun k ↦ weight k * a k)).trans
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (sum_inverse_weight_sq_le M))
          (sizeL2_nonneg _ _))

def energy (M : Finset Wavevector) (a : Wavevector → ℝ) : ℝ :=
  ∑ k ∈ M, (weight k * a k)^2

def dissipation (M : Finset Wavevector) (a : Wavevector → ℝ) : ℝ :=
  energy M (fun k ↦ ‖frequencyVec k‖ * a k)

theorem energy_nonneg (M : Finset Wavevector) (a : Wavevector → ℝ) : 0 ≤ energy M a :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem dissipation_nonneg (M : Finset Wavevector) (a : Wavevector → ℝ) : 0 ≤ dissipation M a :=
  energy_nonneg _ _

def weightedTriad (M : Finset Wavevector) (a : Wavevector → ℝ) : ℝ :=
  ∑ k ∈ M, ∑ l ∈ M,
    cut M (fun q ↦ weight q ^ 2 * a q) (k + l) * a k * (‖frequencyVec l‖ * a l)

theorem weightedTriad_split (M : Finset Wavevector) (a : Wavevector → ℝ)
    (ha : ∀ k, 0 ≤ a k) :
    weightedTriad M a ≤ 2 *
      (triadSum M (fun q ↦ weight q * a q) (fun k ↦ weight k * a k)
          (fun l ↦ ‖frequencyVec l‖ * a l) +
       triadSum M (fun q ↦ weight q * a q) a
          (fun l ↦ weight l * (‖frequencyVec l‖ * a l))) := by
  unfold weightedTriad triadSum
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  by_cases hq : k + l ∈ M
  · simp only [cut, if_pos hq]
    have h := mul_le_mul_of_nonneg_right (weight_add_le k l)
      (mul_nonneg (mul_nonneg (mul_nonneg (weight_pos (k+l)).le (ha (k+l))) (ha k))
        (mul_nonneg (norm_nonneg (frequencyVec l)) (ha l)))
    nlinarith
  · simp [cut, hq]

theorem weightedTriad_le (M : Finset Wavevector) (a : Wavevector → ℝ)
    (ha : ∀ k, 0 ≤ a k) :
    weightedTriad M a ≤ 4 * Real.sqrt latticeMass * energy M a * Real.sqrt (dissipation M a) := by
  let b := fun k ↦ weight k * a k
  let c := fun k ↦ ‖frequencyVec k‖ * a k
  have hc : ∀ k, 0 ≤ c k := fun k ↦ mul_nonneg (norm_nonneg _) (ha k)
  have he : sizeL2 M b ^ 2 = energy M a := Real.sq_sqrt (energy_nonneg M a)
  have hD : sizeL2 M (fun k ↦ weight k * c k) = Real.sqrt (dissipation M a) := rfl
  have h1 := (triadSum_le_rightL1 M b b c (fun k _ ↦ hc k)).trans
    (mul_le_mul_of_nonneg_left (sum_le_weightedL2 M c)
      (mul_nonneg (sizeL2_nonneg M b) (sizeL2_nonneg M b)))
  have h2 := (triadSum_le_leftL1 M b a (fun k ↦ weight k * c k) (fun k _ ↦ ha k)).trans
    (mul_le_mul_of_nonneg_left (sum_le_weightedL2 M a)
      (mul_nonneg (sizeL2_nonneg M b) (sizeL2_nonneg M (fun k ↦ weight k * c k))))
  have h1' : triadSum M b b c ≤ Real.sqrt latticeMass * energy M a * Real.sqrt (dissipation M a) := by
    calc
      _ ≤ _ := h1
      _ = _ := by rw [← he, hD]; ring
  have h2' : triadSum M b a (fun k ↦ weight k * c k) ≤
      Real.sqrt latticeMass * energy M a * Real.sqrt (dissipation M a) := by
    calc
      _ ≤ _ := h2
      _ = _ := by rw [← he, hD]; ring
  have hs := weightedTriad_split M a ha
  change weightedTriad M a ≤ 2 * (triadSum M b b c +
    triadSum M b a (fun k ↦ weight k * c k)) at hs
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeSobolevWeights
