import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSummableOutputTail

/-!
# Joint input and output truncation of summable interactions

An interaction is retained only if both inputs and its output are retained.
The omitted summable majorant tends to zero under finite-set exhaustion.
This accounts for input truncation as well as output projection.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInteractionTruncationTail

open Filter
open scoped Topology
open PeriodicFourierTriad

def retainedPairs (M : Finset Wavevector) : Finset (Wavevector × Wavevector) :=
  (M ×ˢ M).filter (fun p ↦ p.1 + p.2 ∈ M)

theorem mem_retainedPairs (M : Finset Wavevector) (p : Wavevector × Wavevector) :
    p ∈ retainedPairs M ↔ p.1 ∈ M ∧ p.2 ∈ M ∧ p.1 + p.2 ∈ M := by
  simp only [retainedPairs, Finset.mem_filter, Finset.mem_product, and_assoc]

def interactionTail (H : Wavevector × Wavevector → ℝ) (M : Finset Wavevector) : ℝ :=
  ∑' p : Wavevector × Wavevector, if p ∈ retainedPairs M then 0 else H p

theorem interactionTail_nonneg (H : Wavevector × Wavevector → ℝ) (hH : ∀ p, 0 ≤ H p)
    (M : Finset Wavevector) : 0 ≤ interactionTail H M :=
  tsum_nonneg (fun p ↦ by split_ifs <;> simp_all)

theorem summable_interaction_majorant (H : Wavevector × Wavevector → ℝ)
    (hH : ∀ p, 0 ≤ H p) (hSum : Summable H) (M : Finset Wavevector) :
    Summable (fun p : Wavevector × Wavevector ↦ if p ∈ retainedPairs M then 0 else H p) := by
  apply hSum.of_norm_bounded
  intro p
  split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hH p), hH p]

theorem tendsto_interactionTail (H : Wavevector × Wavevector → ℝ)
    (hH : ∀ p, 0 ≤ H p) (hSum : Summable H) :
    Tendsto (interactionTail H) atTop (𝓝 0) := by
  have hp (p : Wavevector × Wavevector) :
      Tendsto (fun M : Finset Wavevector ↦ if p ∈ retainedPairs M then 0 else H p) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({p.1, p.2, p.1 + p.2} : Finset Wavevector)] with M hM
    have hk : p.1 ∈ M := hM (by simp)
    have hl : p.2 ∈ M := hM (by simp)
    have hq : p.1 + p.2 ∈ M := hM (by simp)
    simp [mem_retainedPairs, hk, hl, hq]
  have h := tendsto_tsum_of_dominated_convergence hSum hp
    (Eventually.of_forall (fun (M : Finset Wavevector) (p : Wavevector × Wavevector) ↦
      (show ‖if p ∈ retainedPairs M then (0 : ℝ) else H p‖ ≤ H p by
        split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hH p), hH p])))
  convert h using 1
  · funext M
    rfl
  · simp

theorem exists_interactionTail_lt (H : Wavevector × Wavevector → ℝ)
    (hH : ∀ p, 0 ≤ H p) (hSum : Summable H) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ core : Finset Wavevector, ∀ M : Finset Wavevector, core ⊆ M → interactionTail H M < epsilon :=
  eventually_atTop.mp ((tendsto_interactionTail H hH hSum).eventually (gt_mem_nhds hepsilon))

theorem norm_tsum_sub_finite_le_tail {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : Wavevector × Wavevector → E) (H : Wavevector × Wavevector → ℝ)
    (hSum : Summable H) (hF : ∀ p, ‖F p‖ ≤ H p) (M : Finset Wavevector) :
    ‖(∑' p, F p) - ∑ p ∈ retainedPairs M, F p‖ ≤ interactionTail H M := by
  have hn : Summable (fun p ↦ ‖F p‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hF hSum
  rw [← hn.of_norm.sum_add_tsum_subtype_compl (retainedPairs M), add_sub_cancel_left]
  apply (norm_tsum_le_tsum_norm (hn.subtype _)).trans
  have ht := (hn.subtype (fun p ↦ p ∉ retainedPairs M)).tsum_le_tsum
    (fun p : {p // p ∉ retainedPairs M} ↦ hF p.1) (hSum.subtype _)
  classical
  have he : (∑' p : {p // p ∉ retainedPairs M}, H p.1) = interactionTail H M := by
    change (∑' p : ({p | p ∉ retainedPairs M} : Set (Wavevector × Wavevector)), H p.1) = _
    rw [tsum_subtype]
    apply tsum_congr
    intro p
    by_cases hp : p ∈ retainedPairs M <;> simp [Set.indicator, hp]
  exact ht.trans_eq he

end Mettapedia.FluidDynamics.NavierStokes.PancakeInteractionTruncationTail
