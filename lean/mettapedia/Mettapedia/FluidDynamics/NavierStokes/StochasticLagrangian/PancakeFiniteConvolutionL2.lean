import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLatticeDecayEnvelope

/-!
# Cutoff-independent finite convolution estimates

Translation of a retained set is injective. Cauchy--Schwarz therefore
bounds the finite trilinear convolution without a mode-count factor.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFiniteConvolutionL2

open scoped BigOperators
open PeriodicFourierTriad

def cut (M : Finset Wavevector) (a : Wavevector → ℝ) (q : Wavevector) : ℝ :=
  if q ∈ M then a q else 0

def sizeL2 (M : Finset Wavevector) (a : Wavevector → ℝ) : ℝ :=
  Real.sqrt (∑ q ∈ M, (a q) ^ 2)

theorem sizeL2_nonneg (M : Finset Wavevector) (a : Wavevector → ℝ) : 0 ≤ sizeL2 M a :=
  Real.sqrt_nonneg _

theorem sum_cut_comp_sq_le (M : Finset Wavevector) (a : Wavevector → ℝ)
    (f : Wavevector → Wavevector) (hf : Function.Injective f) :
    (∑ k ∈ M, (cut M a (f k)) ^ 2) ≤ ∑ q ∈ M, (a q) ^ 2 := by
  classical
  let K := M.filter (fun k ↦ f k ∈ M)
  have him : K.image f ⊆ M := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp hk).2
  calc
    _ = ∑ k ∈ K, (a (f k)) ^ 2 := by
      simp [K, cut, Finset.sum_filter, ite_pow]
    _ = ∑ q ∈ K.image f, (a q) ^ 2 := by
      rw [Finset.sum_image (fun _ _ _ _ h ↦ hf h)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg him (fun _ _ _ ↦ sq_nonneg _)

theorem translated_pair_le (M : Finset Wavevector) (a b : Wavevector → ℝ)
    (l : Wavevector) :
    (∑ k ∈ M, cut M a (k + l) * b k) ≤ sizeL2 M a * sizeL2 M b := by
  apply (Real.sum_mul_le_sqrt_mul_sqrt M (fun k ↦ cut M a (k + l)) b).trans
  unfold sizeL2
  exact mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (sum_cut_comp_sq_le M a (fun k ↦ k + l)
      (fun _ _ h ↦ add_right_cancel h))) (Real.sqrt_nonneg _)

def triadSum (M : Finset Wavevector) (a b c : Wavevector → ℝ) : ℝ :=
  ∑ k ∈ M, ∑ l ∈ M, cut M a (k + l) * b k * c l

theorem triadSum_le_rightL1 (M : Finset Wavevector) (a b c : Wavevector → ℝ)
    (hc : ∀ l ∈ M, 0 ≤ c l) :
    triadSum M a b c ≤ sizeL2 M a * sizeL2 M b * ∑ l ∈ M, c l := by
  rw [triadSum, Finset.sum_comm]
  calc
    _ = ∑ l ∈ M, (∑ k ∈ M, cut M a (k + l) * b k) * c l := by simp [Finset.sum_mul]
    _ ≤ ∑ l ∈ M, (sizeL2 M a * sizeL2 M b) * c l := by
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_right (translated_pair_le M a b l) (hc l hl)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem triadSum_swap (M : Finset Wavevector) (a b c : Wavevector → ℝ) :
    triadSum M a b c = triadSum M a c b := by
  rw [triadSum, triadSum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro k hk
  rw [add_comm l k]
  ring

theorem triadSum_le_leftL1 (M : Finset Wavevector) (a b c : Wavevector → ℝ)
    (hb : ∀ k ∈ M, 0 ≤ b k) :
    triadSum M a b c ≤ sizeL2 M a * sizeL2 M c * ∑ k ∈ M, b k := by
  rw [triadSum_swap]
  exact triadSum_le_rightL1 M a c b hb

end Mettapedia.FluidDynamics.NavierStokes.PancakeFiniteConvolutionL2
