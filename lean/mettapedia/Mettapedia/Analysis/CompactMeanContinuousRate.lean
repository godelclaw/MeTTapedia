import Mettapedia.Analysis.CompactMeanDerivative

/-! # Differentiating a compact spatial mean from a continuous time rate -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.CompactMeanContinuousRate

open scoped Topology
open MeasureTheory Set
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [MeasureSpace X] [BorelSpace X] [IsFiniteMeasure (volume : Measure X)]

theorem hasDerivAt_integral (f rate : ℝ → X → ℝ) (a b t : ℝ) (ht : t ∈ Ioo a b)
    (hf : Continuous (fun z : Icc a b × X ↦ f z.1 z.2))
    (hr : Continuous (fun z : Icc a b × X ↦ rate z.1 z.2))
    (hd : ∀ τ ∈ Ioo a b, ∀ x, HasDerivAt (fun r ↦ f r x) (rate τ x) τ) :
    HasDerivAt (fun τ ↦ ∫ x : X, f τ x) (∫ x : X, rate t x) t := by
  haveI : Nonempty (Icc a b) := ⟨⟨t, Ioo_subset_Icc_self ht⟩⟩
  obtain ⟨z₀, hmax⟩ := hr.norm.exists_forall_ge (by simp)
  have hfs (τ : ℝ) (hτ : τ ∈ Icc a b) : Continuous (f τ) :=
    hf.comp ((continuous_const (y := (⟨τ, hτ⟩ : Icc a b))).prodMk continuous_id)
  have hrs (τ : ℝ) (hτ : τ ∈ Icc a b) : Continuous (rate τ) :=
    hr.comp ((continuous_const (y := (⟨τ, hτ⟩ : Icc a b))).prodMk continuous_id)
  have hnear : ∀ᶠ τ in 𝓝 t, τ ∈ Ioo a b := Ioo_mem_nhds ht.1 ht.2
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := f) (F' := rate) (bound := fun _ : X ↦ ‖rate z₀.1 z₀.2‖)
    (Ioo_mem_nhds ht.1 ht.2)
    (hnear.mono (fun τ hτ ↦
      (hfs τ (Ioo_subset_Icc_self hτ)).aestronglyMeasurable))
    ((hfs t (Ioo_subset_Icc_self ht)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hrs t (Ioo_subset_Icc_self ht)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x τ hτ ↦ hmax (⟨τ, Ioo_subset_Icc_self hτ⟩, x)))
    (integrable_const _) (Filter.Eventually.of_forall (fun x τ hτ ↦ hd τ hτ x))
  exact h.2

end Mettapedia.Analysis.CompactMeanContinuousRate
