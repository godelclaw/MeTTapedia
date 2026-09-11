import Mettapedia.Analysis.LocallyLipschitz
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Locally Lipschitz composition with a map smooth along the image -/

set_option autoImplicit false

namespace LocallyLipschitz

open Set Filter

variable {X E F : Type*} [PseudoMetricSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem comp_contDiffAt {f : X → E} {g : E → F} (hf : LocallyLipschitz f)
    (hg : ∀ x, ContDiffAt ℝ 1 g (f x)) : LocallyLipschitz (g ∘ f) := by
  intro x
  obtain ⟨C, s, hs, hC⟩ := hf x
  obtain ⟨D, t, ht, hD⟩ := (hg x).exists_lipschitzOnWith
  refine ⟨D * C, s ∩ f ⁻¹' t, inter_mem hs (hf.continuous.continuousAt ht), ?_⟩
  exact hD.comp (hC.mono inter_subset_left) ((mapsTo_preimage f t).mono_left inter_subset_right)

theorem sqrt {f : X → ℝ} (hf : LocallyLipschitz f) (h : ∀ x, f x ≠ 0) :
    LocallyLipschitz (fun x ↦ Real.sqrt (f x)) :=
  hf.comp_contDiffAt (fun x ↦ Real.contDiffAt_sqrt (h x))

theorem inv_real {f : X → ℝ} (hf : LocallyLipschitz f) (h : ∀ x, f x ≠ 0) :
    LocallyLipschitz (fun x ↦ (f x)⁻¹) :=
  hf.comp_contDiffAt (fun x ↦ contDiffAt_inv ℝ (h x))

theorem div_real {f g : X → ℝ} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g)
    (h : ∀ x, g x ≠ 0) : LocallyLipschitz (fun x ↦ f x / g x) := by
  simpa only [div_eq_mul_inv] using hf.mul_algebra (hg.inv_real h)

end LocallyLipschitz
