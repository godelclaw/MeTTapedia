import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Absolutely convergent bilinear double series

A bounded bilinear map may be applied termwise to two absolutely convergent
series. The product-indexed series is itself absolutely convergent, so the
identity permits regrouping as well as iterated summation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.BilinearSeries

variable {𝕜 E F G ι κ : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
theorem summable_norm_apply (B : E →L[𝕜] F →L[𝕜] G) (f : ι → E) (g : κ → F)
    (hf : Summable (fun i ↦ ‖f i‖)) (hg : Summable (fun j ↦ ‖g j‖)) :
    Summable (fun p : ι × κ ↦ ‖B (f p.1) (g p.2)‖) := by
  have hs := (hf.mul_of_nonneg hg (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)).mul_left ‖B‖
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hs
  intro p
  exact (B.le_opNorm₂ _ _).trans_eq (mul_assoc _ _ _)

theorem hasSum_apply (B : E →L[𝕜] F →L[𝕜] G) (f : ι → E) (g : κ → F)
    (hf : Summable (fun i ↦ ‖f i‖)) (hg : Summable (fun j ↦ ‖g j‖)) :
    HasSum (fun p : ι × κ ↦ B (f p.1) (g p.2)) (B (∑' i, f i) (∑' j, g j)) := by
  have hs := (summable_norm_apply B f g hf hg).of_norm
  have he : (∑' p : ι × κ, B (f p.1) (g p.2)) = B (∑' i, f i) (∑' j, g j) := by
    rw [hs.tsum_prod]
    change (∑' i, ∑' j, B (f i) (g j)) = (B.flip (∑' j, g j)) (∑' i, f i)
    rw [(B.flip (∑' j, g j)).map_tsum hf.of_norm]
    apply tsum_congr
    intro i
    exact ((B (f i)).map_tsum hg.of_norm).symm
  exact he ▸ hs.hasSum

end Mettapedia.Analysis.BilinearSeries
