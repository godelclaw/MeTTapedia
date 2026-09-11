import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! Bounded scalar weights and exact complementary partitions of Banach-space series. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedSeries

variable {𝕜 E ι : Type*} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

theorem summable_smul_of_norm_le (w : ι → 𝕜) (v : ι → E)
    (hv : Summable (fun i ↦ ‖v i‖)) (C : ℝ) (hw : ∀ i, ‖w i‖ ≤ C) :
    Summable (fun i ↦ w i • v i) :=
  (hv.mul_left C).of_norm_bounded (fun i ↦ (norm_smul_le _ _).trans
    (mul_le_mul_of_nonneg_right (hw i) (norm_nonneg _)))

theorem tsum_smul_add_complement (w : ι → 𝕜) (v : ι → E)
    (hv : Summable (fun i ↦ ‖v i‖)) (C D : ℝ)
    (hw : ∀ i, ‖w i‖ ≤ C) (hc : ∀ i, ‖1 - w i‖ ≤ D) :
    (∑' i, w i • v i) + (∑' i, (1 - w i) • v i) = ∑' i, v i := by
  rw [← (summable_smul_of_norm_le w v hv C hw).tsum_add
    (summable_smul_of_norm_le (fun i ↦ 1 - w i) v hv D hc)]
  apply tsum_congr
  intro i
  rw [← add_smul]
  simp

end Mettapedia.Analysis.WeightedSeries
