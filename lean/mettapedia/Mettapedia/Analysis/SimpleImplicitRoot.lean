import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Smoothness of a continuous simple root

A continuous choice of roots of a smooth scalar equation is smooth near
any point where the derivative in the root variable is nonzero. Local
uniqueness identifies the given root with mathlib's implicit function.
-/

set_option autoImplicit false
open scoped Topology ContDiff

namespace Mettapedia.Analysis

theorem contDiffAt_of_simple_implicit_root {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ∞ω} {f : E × ℝ → ℝ} {r : E → ℝ} {x : E} {c : ℝ}
    (hf : ContDiffAt ℝ n f (x, r x)) (hn : n ≠ 0)
    (hr : ContinuousAt r x) (hroot : ∀ᶠ y in 𝓝 x, f (y, r y) = 0)
    (hd : HasDerivAt (fun z ↦ f (x, z)) c (r x)) (hc : c ≠ 0) :
    ContDiffAt ℝ n r x := by
  have hpartial : fderiv ℝ f (x, r x) ∘L ContinuousLinearMap.inr ℝ E ℝ =
      c • ContinuousLinearMap.id ℝ ℝ := by
    have h := (hf.hasStrictFDerivAt hn).hasFDerivAt.comp (r x)
      (hasFDerivAt_prodMk_right x (r x))
    convert h.unique hd.hasFDerivAt using 1
    ext
    simp
  have hi : (fderiv ℝ f (x, r x) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := by
    rw [hpartial]
    refine ⟨ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ) (Units.mk0 c hc), ?_⟩
    ext
    simp
  have he := hf.eventually_apply_eq_iff_implicitFunction hn hi
  have he' := (continuousAt_id.prodMk hr).eventually he
  apply (hf.contDiffAt_implicitFunction hn hi).congr_of_eventuallyEq
  filter_upwards [hroot, he'] with y hy heq
  exact (heq.mp (hy.trans hroot.self_of_nhds.symm)).symm

end Mettapedia.Analysis
