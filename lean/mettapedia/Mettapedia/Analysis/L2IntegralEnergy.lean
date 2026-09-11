import Mathlib.MeasureTheory.Function.L2Space

/-! Exact conversion between L² norms and integrals of squared norms. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.L2IntegralEnergy

open MeasureTheory Filter
open scoped Topology

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sq (f : Lp E 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem norm_toLp_sq (f : α → E) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

theorem norm_sub_toLp_sq (f g : α → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, ‖f x - g x‖ ^ 2 ∂μ := by
  rw [norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp] with x hx hfx hgx
  simp only [hx, Pi.sub_apply, hfx, hgx]

theorem tendsto_toLp_of_integral_sub_sq {ι : Type*} {l : Filter ι}
    (f : ι → α → E) (g : α → E) (hf : ∀ i, MemLp (f i) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun i ↦ ∫ x, ‖f i x - g x‖ ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ (hf i).toLp (f i)) l (𝓝 (hg.toLp g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  have he (i : ι) : (∫ x, ‖f i x - g x‖ ^ 2 ∂μ) =
      ‖(hf i).toLp (f i) - hg.toLp g‖ ^ 2 := (norm_sub_toLp_sq _ _ _ _).symm
  simpa only [Function.comp_def, he, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs

omit [InnerProductSpace ℝ E] in
theorem toLp_eq_iff (f g : α → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    hf.toLp f = hg.toLp g ↔ f =ᵐ[μ] g := by
  constructor
  · intro h
    exact hf.coeFn_toLp.symm.trans ((Filter.EventuallyEq.of_eq (congrArg (fun v : Lp E 2 μ ↦ ⇑v) h)).trans
      hg.coeFn_toLp)
  · intro h
    exact Lp.ext (hf.coeFn_toLp.trans (h.trans hg.coeFn_toLp.symm))

end Mettapedia.Analysis.L2IntegralEnergy
