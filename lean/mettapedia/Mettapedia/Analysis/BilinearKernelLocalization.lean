import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bilinear localization with the input weights retained

The two differences are kept with their own input vectors. This is the
pointwise algebra used by a physical kernel commutator; it does not require
either scalar cutoff to have an unweighted Sobolev derivative.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.BilinearKernelLocalization

open MeasureTheory

variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem smul_sub_apply_smul (B : E →L[𝕜] F →L[𝕜] G) (c d a b : 𝕜) (u : E) (v : F) :
    (c * d) • B u v - B (a • u) (b • v) = (c * d - a * b) • B u v := by
  simp only [map_smul, smul_apply, smul_smul, sub_smul, mul_comm a b]

theorem norm_smul_sub_apply_smul_le (B : E →L[𝕜] F →L[𝕜] G) (c d a b : 𝕜) (u : E) (v : F) :
    ‖(c * d) • B u v - B (a • u) (b • v)‖ ≤
      ‖B‖ * (‖d‖ * (‖c - a‖ * ‖u‖) * ‖v‖ + ‖a‖ * ‖u‖ * (‖d - b‖ * ‖v‖)) := by
  have he : c * d - a * b = d * (c - a) + a * (d - b) := by ring
  have hd : ‖c * d - a * b‖ ≤ ‖d‖ * ‖c - a‖ + ‖a‖ * ‖d - b‖ := by
    rw [he]
    simpa only [norm_mul] using norm_add_le (d * (c - a)) (a * (d - b))
  have hB : ‖B u v‖ ≤ ‖B‖ * ‖u‖ * ‖v‖ :=
    (B u).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (B.le_opNorm u) (norm_nonneg v))
  rw [smul_sub_apply_smul, norm_smul]
  exact (mul_le_mul hd hB (norm_nonneg _) (by positivity)).trans_eq (by ring)

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable [NormedSpace ℝ G] [IsScalarTower ℝ 𝕜 G]

theorem smul_integral_sub_integral_apply_smul
    (K : α → E →L[𝕜] F →L[𝕜] G) (u : α → E) (v : α → F)
    (a b : α → 𝕜) (c d : 𝕜)
    (hbase : Integrable (fun q ↦ K q (u q) (v q)) μ)
    (hlocal : Integrable (fun q ↦ K q (a q • u q) (b q • v q)) μ) :
    (c * d) • (∫ q, K q (u q) (v q) ∂μ) -
      (∫ q, K q (a q • u q) (b q • v q) ∂μ) =
      ∫ q, (c * d - a q * b q) • K q (u q) (v q) ∂μ := by
  have hs : Integrable (fun q ↦ (c * d) • K q (u q) (v q)) μ := hbase.smul (c * d)
  rw [← integral_smul, ← integral_sub hs hlocal]
  apply integral_congr_ae
  filter_upwards [] with q
  exact smul_sub_apply_smul (K q) c d (a q) (b q) (u q) (v q)

theorem norm_smul_integral_sub_integral_apply_smul_le
    (K : α → E →L[𝕜] F →L[𝕜] G) (u : α → E) (v : α → F)
    (a b : α → 𝕜) (c d : 𝕜)
    (hbase : Integrable (fun q ↦ K q (u q) (v q)) μ)
    (hlocal : Integrable (fun q ↦ K q (a q • u q) (b q • v q)) μ)
    (hdom : Integrable (fun q ↦ ‖K q‖ *
      (‖d‖ * (‖c - a q‖ * ‖u q‖) * ‖v q‖ + ‖a q‖ * ‖u q‖ * (‖d - b q‖ * ‖v q‖))) μ) :
    ‖(c * d) • (∫ q, K q (u q) (v q) ∂μ) -
      (∫ q, K q (a q • u q) (b q • v q) ∂μ)‖ ≤
      ∫ q, ‖K q‖ * (‖d‖ * (‖c - a q‖ * ‖u q‖) * ‖v q‖ +
        ‖a q‖ * ‖u q‖ * (‖d - b q‖ * ‖v q‖)) ∂μ := by
  have hs : Integrable (fun q ↦ (c * d) • K q (u q) (v q)) μ := hbase.smul (c * d)
  rw [← integral_smul, ← integral_sub hs hlocal]
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono (hs.sub hlocal).norm hdom
      (fun q ↦ norm_smul_sub_apply_smul_le (K q) c d (a q) (b q) (u q) (v q)))

end Mettapedia.Analysis.BilinearKernelLocalization
