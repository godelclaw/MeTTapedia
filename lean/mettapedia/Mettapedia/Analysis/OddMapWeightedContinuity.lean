import Mettapedia.Analysis.OddMapLineEstimate
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Continuity of weighted norms along unoriented directions

The unit representative need not be measurable or continuous. A continuous
comparison field controls its weighted line distance. Oddness and a uniform
direction estimate then give continuity of the weighted output norm, even
where the weight vanishes. Spatial continuity is needed only for each fixed
unit direction.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.OddMapWeightedContinuity

open Filter
open scoped Topology
open OddMapLineEstimate

variable {X E F P : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup P]

theorem continuous_weighted_norm (f : E → X → F)
    (hodd : ∀ x e, f (-e) x = -f e x) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ x e r, ‖e‖ = 1 → ‖r‖ = 1 → ‖f e x - f r x‖ ≤ L * ‖e - r‖)
    (hx : ∀ e, ‖e‖ = 1 → Continuous (f e))
    (a : X → ℝ) (ha : Continuous a) (e : X → E) (he : ∀ x, ‖e x‖ = 1)
    (p : X → P) (hp : Continuous p)
    (hline : ∀ x y, a x ^ 2 * min (‖e x - e y‖ ^ 2) (‖e x + e y‖ ^ 2) ≤
      2 * ‖p x - p y‖ ^ 2) :
    Continuous (fun x ↦ a x * ‖f (e x) x‖) := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto (fun y ↦ a y * ‖f (e y) y‖) (𝓝 x) (𝓝 (a x * ‖f (e x) x‖))
  let g : X → ℝ := fun y ↦ a y * (‖f (e y) y‖ - ‖f (e x) y‖)
  have hg : Tendsto g (𝓝 x) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hlim : Tendsto (fun y ↦ 2 * L * ‖p y - p x‖) (𝓝 x) (𝓝 0) := by
      simpa only [sub_self, norm_zero, mul_zero] using
        ((hp.tendsto x).sub_const (p x)).norm.const_mul (2 * L)
    apply squeeze_zero (fun _ ↦ norm_nonneg _) _ hlim
    intro y
    simpa only [g, Real.norm_eq_abs] using
      abs_weight_mul_norm_sub_norm_le (fun d ↦ f d y) (hodd y) L hL (hf y)
        (e y) (e x) (he y) (he x) (a y) ‖p y - p x‖ (norm_nonneg _) (hline y x)
  have hb := (ha.tendsto x).mul ((hx (e x) (he x)).norm.tendsto x)
  have heq (y : X) : g y + a y * ‖f (e x) y‖ = a y * ‖f (e y) y‖ := by
    dsimp only [g]
    ring
  simpa only [heq, zero_add] using hg.add hb

end Mettapedia.Analysis.OddMapWeightedContinuity
