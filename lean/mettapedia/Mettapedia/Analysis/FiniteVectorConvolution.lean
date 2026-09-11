import Mettapedia.Analysis.FiniteMultiplierLocalization

/-! # Linear identities and Young bounds for collected finite convolutions -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.FiniteMultiplierLocalization

open scoped BigOperators

variable {G E 𝕜 : Type*} [AddCommGroup G] [DecidableEq G] [NormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem vectorConvolution_sub (A P : Finset G) (c : G → 𝕜) (w v : G → E) (q : G) :
    vectorConvolution A P c (w - v) q =
      vectorConvolution A P c w q - vectorConvolution A P c v q := by
  simp only [vectorConvolution, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

theorem sum_norm_vectorConvolution_le (A P Q : Finset G) (c : G → 𝕜) (w : G → E)
    (hQ : ∀ a ∈ A, ∀ p ∈ P, a + p ∈ Q) :
    (∑ q ∈ Q, ‖vectorConvolution A P c w q‖) ≤
      (∑ a ∈ A, ‖c a‖) * ∑ p ∈ P, ‖w p‖ := by
  have h := Finset.sum_le_sum (fun q (_ : q ∈ Q) ↦
    norm_sum_le ((A ×ˢ P).filter (fun ap ↦ ap.1 + ap.2 = q))
      (fun ap ↦ c ap.1 • w ap.2))
  rw [Finset.sum_fiberwise_of_maps_to
    (fun ap hap ↦ hQ _ (Finset.mem_product.mp hap).1 _ (Finset.mem_product.mp hap).2)] at h
  simpa only [vectorConvolution, norm_smul, Finset.sum_product,
    ← Finset.mul_sum, ← Finset.sum_mul] using h

theorem sum_norm_vectorConvolution_sq_le (A P Q : Finset G) (c : G → 𝕜) (w : G → E)
    (hQ : ∀ a ∈ A, ∀ p ∈ P, a + p ∈ Q) :
    (∑ q ∈ Q, ‖vectorConvolution A P c w q‖ ^ 2) ≤
      (∑ a ∈ A, ‖c a‖) ^ 2 * ∑ p ∈ P, ‖w p‖ ^ 2 :=
  FiniteConvolutionEnergy.sum_norm_sq_le A P Q (fun a ↦ ‖c a‖) (fun p ↦ ‖w p‖)
    (fun a p ↦ c a • w p) (fun _ _ ↦ norm_nonneg _)
    (fun _ _ _ _ ↦ le_of_eq (norm_smul _ _)) hQ

end Mettapedia.Analysis.FiniteMultiplierLocalization
