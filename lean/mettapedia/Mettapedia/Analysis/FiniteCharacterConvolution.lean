import Mettapedia.Analysis.FiniteVectorConvolution
import Mettapedia.Analysis.FiniteFiberLinearMap

/-! # Evaluation of collected convolution against a multiplicative character -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.FiniteMultiplierLocalization

open scoped BigOperators

variable {G E 𝕜 : Type*} [AddCommGroup G] [DecidableEq G] [NormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem sum_character_smul_vectorConvolution (A P Q : Finset G)
    (c χ : G → 𝕜) (w : G → E) (hχ : ∀ a p, χ (a + p) = χ a * χ p)
    (hQ : ∀ a ∈ A, ∀ p ∈ P, a + p ∈ Q) :
    (∑ q ∈ Q, χ q • vectorConvolution A P c w q) =
      (∑ a ∈ A, χ a * c a) • ∑ p ∈ P, χ p • w p := by
  have h := sum_apply_fiberwise (A ×ˢ P) Q (fun ap ↦ ap.1 + ap.2)
    (fun ap ↦ c ap.1 • w ap.2) (fun q ↦ χ q • (LinearMap.id : E →ₗ[𝕜] E))
    (fun ap hap ↦ hQ _ (Finset.mem_product.mp hap).1 _ (Finset.mem_product.mp hap).2)
  change (∑ q ∈ Q, χ q • vectorConvolution A P c w q) =
    ∑ ap ∈ A ×ˢ P, χ (ap.1 + ap.2) • (c ap.1 • w ap.2) at h
  rw [h, Finset.sum_smul]
  simp only [Finset.sum_product, hχ, smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro p _
  rw [show χ a * χ p * c a = χ a * c a * χ p by ring]

end Mettapedia.Analysis.FiniteMultiplierLocalization
