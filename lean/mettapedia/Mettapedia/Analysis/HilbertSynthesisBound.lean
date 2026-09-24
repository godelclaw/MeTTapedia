import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Bessel bounds from finite Hilbert-space synthesis

A square-norm bound on all finite syntheses gives the same bound for
the square sum of their coefficient adjoints. No orthogonal basis or
choice of a representative for the target field is required.
-/

namespace Mettapedia.Analysis.HilbertSynthesisBound

open scoped RealInnerProductSpace

variable {ι E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem sum_norm_adjoint_sq_le (A : ι → E →L[ℝ] H) (P : Finset ι) (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ a : ι → E, ‖∑ i ∈ P, A i (a i)‖ ^ 2 ≤ K * ∑ i ∈ P, ‖a i‖ ^ 2)
    (F : H) : (∑ i ∈ P, ‖(A i).adjoint F‖ ^ 2) ≤ K * ‖F‖ ^ 2 := by
  let S := ∑ i ∈ P, ‖(A i).adjoint F‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have he : ⟪∑ i ∈ P, A i ((A i).adjoint F), F⟫ = S := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    exact (ContinuousLinearMap.adjoint_inner_right (A i) ((A i).adjoint F) F).symm.trans
      (real_inner_self_eq_norm_sq _)
  have hi := real_inner_le_norm (∑ i ∈ P, A i ((A i).adjoint F)) F
  rw [he] at hi
  have hs := pow_le_pow_left₀ hS hi 2
  rw [mul_pow] at hs
  have hmul := mul_le_mul_of_nonneg_right (hA (fun i ↦ (A i).adjoint F)) (sq_nonneg ‖F‖)
  change S ≤ K * ‖F‖ ^ 2
  change ‖∑ i ∈ P, A i ((A i).adjoint F)‖ ^ 2 * ‖F‖ ^ 2 ≤ K * S * ‖F‖ ^ 2 at hmul
  by_cases hz : S = 0
  · rw [hz]
    positivity
  · have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
    nlinarith

theorem summable_norm_adjoint_sq (A : ι → E →L[ℝ] H) (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ (P : Finset ι) (a : ι → E),
      ‖∑ i ∈ P, A i (a i)‖ ^ 2 ≤ K * ∑ i ∈ P, ‖a i‖ ^ 2) (F : H) :
    Summable (fun i ↦ ‖(A i).adjoint F‖ ^ 2) :=
  summable_of_sum_le (fun _ ↦ sq_nonneg _)
    (fun P ↦ sum_norm_adjoint_sq_le A P K hK (hA P) F)

theorem tsum_norm_adjoint_sq_le (A : ι → E →L[ℝ] H) (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ (P : Finset ι) (a : ι → E),
      ‖∑ i ∈ P, A i (a i)‖ ^ 2 ≤ K * ∑ i ∈ P, ‖a i‖ ^ 2) (F : H) :
    (∑' i, ‖(A i).adjoint F‖ ^ 2) ≤ K * ‖F‖ ^ 2 :=
  (summable_norm_adjoint_sq A K hK hA F).tsum_le_of_sum_le
    (fun P ↦ sum_norm_adjoint_sq_le A P K hK (hA P) F)

end Mettapedia.Analysis.HilbertSynthesisBound
