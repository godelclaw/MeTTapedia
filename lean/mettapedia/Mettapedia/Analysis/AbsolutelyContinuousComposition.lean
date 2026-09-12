import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! # Lipschitz composition and pairing of absolutely continuous paths -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AbsolutelyContinuousComposition

open Filter
open scoped NNReal
variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  {u : ℝ → X} {v : ℝ → Y} {a b : ℝ}

theorem comp_lipschitz {F : X → Y} {K : ℝ≥0} (hF : LipschitzWith K F)
    (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ F (u t)) a b := by
  apply squeeze_zero (fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)) ?_
    (by simpa only [mul_zero] using Filter.Tendsto.const_mul (K : ℝ) hu)
  intro I
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun _ _ ↦ hF.dist_le_mul _ _)

theorem prodMk (hu : AbsolutelyContinuousOnInterval u a b)
    (hv : AbsolutelyContinuousOnInterval v a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ (u t, v t)) a b := by
  apply squeeze_zero (fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)) ?_
    (by simpa only [add_zero] using Filter.Tendsto.add hu hv)
  intro I
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Prod.dist_eq]
  exact max_le (le_add_of_nonneg_right dist_nonneg) (le_add_of_nonneg_left dist_nonneg)

theorem of_locallyLipschitz (hu : LocallyLipschitz u) :
    AbsolutelyContinuousOnInterval u a b := by
  obtain ⟨K, hK⟩ := hu.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc : IsCompact (Set.uIcc a b))
  exact hK.absolutelyContinuousOnInterval

theorem congr {w : ℝ → X} (hu : AbsolutelyContinuousOnInterval u a b)
    (h : Set.EqOn u w (Set.uIcc a b)) : AbsolutelyContinuousOnInterval w a b := by
  rw [absolutelyContinuousOnInterval_iff] at hu ⊢
  intro ε hε
  obtain ⟨δ, hδ, hsum⟩ := hu ε hε
  refine ⟨δ, hδ, fun I hI hlen ↦ ?_⟩
  have he : (∑ i ∈ Finset.range I.1, dist (w (I.2 i).1) (w (I.2 i).2)) =
      ∑ i ∈ Finset.range I.1, dist (u (I.2 i).1) (u (I.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [h ((hI.1 i hi).1), h ((hI.1 i hi).2)]
  rw [he]
  exact hsum I hI hlen

end Mettapedia.Analysis.AbsolutelyContinuousComposition
