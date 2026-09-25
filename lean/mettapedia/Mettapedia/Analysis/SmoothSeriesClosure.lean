import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Smoothness of series on the closure of an open convex set

Mathlib's `contDiff_tsum` gives smoothness of a series on the whole space from
summable bounds on the iterated derivatives, and `hasFDerivAt_tsum_of_isPreconnected`
differentiates termwise on an open preconnected set. This module proves the
analogue on the closure `s` of an open convex set with bounds on the iterated
derivatives *within* `s`, such as a closed time half-line or slab times space.
Termwise differentiation holds on the interior, and the derivative extends to
boundary points because the derivative series is continuous up to the
boundary (`hasFDerivWithinAt_closure_of_tendsto_fderiv`).
-/

open Set Filter
open scoped Topology ContDiff

namespace Mettapedia.Analysis.SmoothSeriesClosure

variable {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

/-- **Termwise differentiation on the closure of an open convex set.** -/
theorem hasFDerivWithinAt_tsum_closure {U : Set E} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hne : U.Nonempty) {g : α → E → F} {g' : α → E → E →L[ℝ] F} {u : α → ℝ} (hu : Summable u)
    (hg : ∀ i, ∀ x ∈ closure U, HasFDerivWithinAt (g i) (g' i x) (closure U) x)
    (hg'c : ∀ i, ContinuousOn (g' i) (closure U))
    (hg'b : ∀ i, ∀ x ∈ closure U, ‖g' i x‖ ≤ u i)
    (hgc : ContinuousOn (fun x ↦ ∑' i, g i x) (closure U))
    (hsum : ∀ x ∈ closure U, Summable (fun i ↦ g i x)) {x : E} (hx : x ∈ closure U) :
    HasFDerivWithinAt (fun y ↦ ∑' i, g i y) (∑' i, g' i x) (closure U) x := by
  obtain ⟨y₀, hy₀⟩ := hne
  have hat : ∀ y ∈ U, HasFDerivAt (fun z ↦ ∑' i, g i z) (∑' i, g' i y) y := by
    intro y hy
    refine hasFDerivAt_tsum_of_isPreconnected hu hU hUc.isPreconnected
      (fun i z hz ↦ (hg i z (subset_closure hz)).hasFDerivAt
        (mem_of_superset (hU.mem_nhds hz) subset_closure))
      (fun i z hz ↦ hg'b i z (subset_closure hz)) hy₀ (hsum y₀ (subset_closure hy₀)) hy
  have hdiff : DifferentiableOn ℝ (fun z ↦ ∑' i, g i z) U :=
    fun y hy ↦ (hat y hy).differentiableAt.differentiableWithinAt
  have hcont' : ContinuousOn (fun z ↦ ∑' i, g' i z) (closure U) :=
    continuousOn_tsum hg'c hu hg'b
  refine hasFDerivWithinAt_closure_of_tendsto_fderiv hdiff hUc hU
    (fun y hy ↦ (hgc y hy).mono subset_closure) ?_
  have ht : Tendsto (fun z ↦ ∑' i, g' i z) (𝓝[U] x) (𝓝 (∑' i, g' i x)) :=
    ((hcont' x hx).mono subset_closure).tendsto
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hat z hz).fderiv.symm

/-- Iterated within-derivatives of a series on the closure of an open convex set
are the series of the iterated within-derivatives. -/
theorem iteratedFDerivWithin_tsum_closure {U : Set E} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hne : U.Nonempty) {f : α → E → F} {N : ℕ∞} (hf : ∀ i, ContDiffOn ℝ N (f i) (closure U))
    {v : ℕ → α → ℝ} (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (hb : ∀ k : ℕ, (k : ℕ∞) ≤ N → ∀ i, ∀ x ∈ closure U,
      ‖iteratedFDerivWithin ℝ k (f i) (closure U) x‖ ≤ v k i) :
    ∀ m : ℕ, (m : ℕ∞) ≤ N → ∀ x ∈ closure U,
      iteratedFDerivWithin ℝ m (fun y ↦ ∑' i, f i y) (closure U) x =
        ∑' i, iteratedFDerivWithin ℝ m (f i) (closure U) x := by
  have hs : UniqueDiffOn ℝ (closure U) :=
    uniqueDiffOn_convex hUc.closure (hne.mono (interior_maximal subset_closure hU))
  intro m
  induction m with
  | zero =>
    intro _ x _
    simp only [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
  | succ m ih =>
    intro hm x hx
    have hm' : (m : ℕ∞) ≤ N := le_trans (by exact_mod_cast Nat.le_succ m) hm
    have hlt : (m : WithTop ℕ∞) < (N : WithTop ℕ∞) := by
      exact_mod_cast lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) hm
    set g : α → E → (ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F) :=
      fun i ↦ iteratedFDerivWithin ℝ m (f i) (closure U) with hgdef
    have hgd : ∀ i, DifferentiableOn ℝ (g i) (closure U) := fun i ↦
      (hf i).differentiableOn_iteratedFDerivWithin hlt hs
    have hcurry : ∀ i y, ‖fderivWithin ℝ (g i) (closure U) y‖ =
        ‖iteratedFDerivWithin ℝ (m + 1) (f i) (closure U) y‖ := by
      intro i y
      rw [hgdef, fderivWithin_iteratedFDerivWithin, Function.comp_apply,
        LinearIsometryEquiv.norm_map]
    have hcontd : ∀ i, ContinuousOn (fun y ↦ fderivWithin ℝ (g i) (closure U) y) (closure U) := by
      intro i
      have h := (hf i).continuousOn_iteratedFDerivWithin (m := m + 1) (by exact_mod_cast hm) hs
      have e : (fun y ↦ fderivWithin ℝ (g i) (closure U) y) =
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F) ∘
            iteratedFDerivWithin ℝ (m + 1) (f i) (closure U) := by
        rw [hgdef, fderivWithin_iteratedFDerivWithin]
      rw [e]
      exact (LinearIsometryEquiv.continuous _).comp_continuousOn h
    have hgc : ContinuousOn (fun y ↦ ∑' i, g i y) (closure U) :=
      continuousOn_tsum (fun i ↦ (hf i).continuousOn_iteratedFDerivWithin
        (by exact_mod_cast hm') hs) (hv m hm') (fun i y hy ↦ hb m hm' i y hy)
    have hsum : ∀ y ∈ closure U, Summable (fun i ↦ g i y) := fun y hy ↦
      (hv m hm').of_norm_bounded (fun i ↦ hb m hm' i y hy)
    have hD := hasFDerivWithinAt_tsum_closure hU hUc hne (hv (m + 1) hm)
      (fun i y hy ↦ (hgd i y hy).hasFDerivWithinAt) hcontd
      (fun i y hy ↦ (hcurry i y).le.trans (hb (m + 1) hm i y hy)) hgc hsum hx
    have hcongr : fderivWithin ℝ (iteratedFDerivWithin ℝ m (fun y ↦ ∑' i, f i y) (closure U))
        (closure U) x = fderivWithin ℝ (fun y ↦ ∑' i, g i y) (closure U) x := by
      refine fderivWithin_congr' (fun y hy ↦ ?_) hx
      exact ih hm' y hy
    rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply, hcongr,
      hD.fderivWithin (hs x hx)]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F).symm.toContinuousLinearEquiv.map_tsum

/-- **Smoothness of a series on the closure of an open convex set.** -/
theorem contDiffOn_tsum_closure {U : Set E} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hne : U.Nonempty) {f : α → E → F} {N : ℕ∞} (hf : ∀ i, ContDiffOn ℝ N (f i) (closure U))
    {v : ℕ → α → ℝ} (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (hb : ∀ k : ℕ, (k : ℕ∞) ≤ N → ∀ i, ∀ x ∈ closure U,
      ‖iteratedFDerivWithin ℝ k (f i) (closure U) x‖ ≤ v k i) :
    ContDiffOn ℝ N (fun x ↦ ∑' i, f i x) (closure U) := by
  have hs : UniqueDiffOn ℝ (closure U) :=
    uniqueDiffOn_convex hUc.closure (hne.mono (interior_maximal subset_closure hU))
  have hformula := iteratedFDerivWithin_tsum_closure hU hUc hne hf hv hb
  refine contDiffOn_of_continuousOn_differentiableOn (fun m hm ↦ ?_) (fun m hm ↦ ?_)
  · have hc : ContinuousOn (fun x ↦ ∑' i, iteratedFDerivWithin ℝ m (f i) (closure U) x)
        (closure U) :=
      continuousOn_tsum (fun i ↦ (hf i).continuousOn_iteratedFDerivWithin (by exact_mod_cast hm) hs)
        (hv m hm) (fun i y hy ↦ hb m hm i y hy)
    exact hc.congr fun x hx ↦ hformula m hm x hx
  · have hm' : (m : ℕ∞) ≤ N := hm.le
    have hlt : (m : WithTop ℕ∞) < (N : WithTop ℕ∞) := by exact_mod_cast hm
    have hm1 : ((m + 1 : ℕ) : ℕ∞) ≤ N := by exact_mod_cast Order.add_one_le_of_lt hm
    set g : α → E → (ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F) :=
      fun i ↦ iteratedFDerivWithin ℝ m (f i) (closure U) with hgdef
    have hgd : ∀ i, DifferentiableOn ℝ (g i) (closure U) := fun i ↦
      (hf i).differentiableOn_iteratedFDerivWithin hlt hs
    have hcurry : ∀ i y, ‖fderivWithin ℝ (g i) (closure U) y‖ =
        ‖iteratedFDerivWithin ℝ (m + 1) (f i) (closure U) y‖ := by
      intro i y
      rw [hgdef, fderivWithin_iteratedFDerivWithin, Function.comp_apply,
        LinearIsometryEquiv.norm_map]
    have hcontd : ∀ i, ContinuousOn (fun y ↦ fderivWithin ℝ (g i) (closure U) y) (closure U) := by
      intro i
      have h := (hf i).continuousOn_iteratedFDerivWithin (m := m + 1) (by exact_mod_cast hm1) hs
      have e : (fun y ↦ fderivWithin ℝ (g i) (closure U) y) =
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F) ∘
            iteratedFDerivWithin ℝ (m + 1) (f i) (closure U) := by
        rw [hgdef, fderivWithin_iteratedFDerivWithin]
      rw [e]
      exact (LinearIsometryEquiv.continuous _).comp_continuousOn h
    have hgc : ContinuousOn (fun y ↦ ∑' i, g i y) (closure U) :=
      continuousOn_tsum (fun i ↦ (hf i).continuousOn_iteratedFDerivWithin
        (by exact_mod_cast hm') hs) (hv m hm') (fun i y hy ↦ hb m hm' i y hy)
    have hsum : ∀ y ∈ closure U, Summable (fun i ↦ g i y) := fun y hy ↦
      (hv m hm').of_norm_bounded (fun i ↦ hb m hm' i y hy)
    intro x hx
    have hD := hasFDerivWithinAt_tsum_closure hU hUc hne (hv (m + 1) hm1)
      (fun i y hy ↦ (hgd i y hy).hasFDerivWithinAt) hcontd
      (fun i y hy ↦ (hcurry i y).le.trans (hb (m + 1) hm1 i y hy)) hgc hsum hx
    exact (hD.differentiableWithinAt).congr (fun y hy ↦ hformula m hm' y hy) (hformula m hm' x hx)

end Mettapedia.Analysis.SmoothSeriesClosure
