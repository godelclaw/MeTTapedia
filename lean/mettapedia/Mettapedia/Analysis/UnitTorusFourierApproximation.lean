import Mettapedia.Analysis.UnitTorusFourierEnergy
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite Fourier approximation in L² and in the uniform norm

Actual-coefficient projections converge in L². Separately, vector fields
have uniform polynomial approximants with a common finite frequency set.
No assertion of uniform convergence of ordinary Fourier partial sums is made.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusFourierApproximation

open MeasureTheory UnitAddTorus Filter Set Submodule
open scoped Topology

variable {d ι : Type*} [Fintype d] [Fintype ι]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def projection (f : C(UnitAddTorus d, ℂ)) (P : Finset (d → ℤ)) : C(UnitAddTorus d, ℂ) :=
  ∑ q ∈ P, mFourierCoeff f q • mFourier q

theorem norm_toLp_sq (f : C(UnitAddTorus d, ℂ)) :
    ‖f.toLp 2 volume ℂ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp (p := 2) (𝕜 := ℂ) volume] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem toLp_projection (f : C(UnitAddTorus d, ℂ)) (P : Finset (d → ℤ)) :
    (projection f P).toLp 2 volume ℂ = ∑ q ∈ P, mFourierCoeff f q • mFourierLp 2 q := by
  simp only [projection, map_sum, map_smul]

theorem integral_projection_error_eq (f : C(UnitAddTorus d, ℂ)) (P : Finset (d → ℤ)) :
    (∫ x, ‖projection f P x - f x‖ ^ 2) =
      ‖(∑ q ∈ P, mFourierCoeff f q • mFourierLp 2 q) - f.toLp 2 volume ℂ‖ ^ 2 := by
  rw [← toLp_projection, ← map_sub, norm_toLp_sq]
  rfl

theorem tendsto_integral_projection_error (f : C(UnitAddTorus d, ℂ)) :
    Tendsto (fun P : Finset (d → ℤ) ↦ ∫ x, ‖projection f P x - f x‖ ^ 2) atTop (𝓝 0) := by
  have hs : Tendsto (fun P : Finset (d → ℤ) ↦
      ∑ q ∈ P, mFourierCoeff (f.toLp 2 volume ℂ) q • mFourierLp 2 q) atTop (𝓝 (f.toLp 2 volume ℂ)) :=
    hasSum_mFourier_series_L2 (f.toLp 2 volume ℂ)
  have h := hs.sub_const (f.toLp 2 volume ℂ)
  simp only [mFourierCoeff_toLp, sub_self] at h
  simpa only [integral_projection_error_eq, norm_zero, zero_pow (by decide : 2 ≠ 0)] using h.norm.pow 2

theorem exists_sum_integral_projection_error_lt {ι : Type*} [Fintype ι]
    (f : ι → C(UnitAddTorus d, ℂ)) (delta : ℝ) (hd : 0 < delta) :
    ∃ P : Finset (d → ℤ), (∑ i, ∫ x, ‖projection (f i) P x - f i x‖ ^ 2) < delta := by
  have h := tendsto_finsetSum Finset.univ (fun i _ ↦ tendsto_integral_projection_error (f i))
  simp only [Finset.sum_const_zero] at h
  exact (h.eventually (gt_mem_nhds hd)).exists


theorem exists_scalar_approximation (f : C(UnitAddTorus d, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : (d → ℤ) →₀ ℂ, ‖f - c.sum (fun q a ↦ a • mFourier q)‖ < ε := by
  have hf : f ∈ (span ℂ (range (mFourier (d := d)))).topologicalClosure := by
    rw [span_mFourier_closure_eq_top]
    trivial
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf ε hε
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hg
  refine ⟨c, ?_⟩
  rw [hc]
  simpa only [dist_eq_norm] using hfg

def polynomial (P : Finset (d → ℤ)) (v : (d → ℤ) → EuclideanSpace ℂ ι) :
    C(UnitAddTorus d, EuclideanSpace ℂ ι) :=
  ∑ q ∈ P, ⟨fun x ↦ mFourier q x • v q, (mFourier q).continuous.smul continuous_const⟩

@[simp] theorem polynomial_apply (P : Finset (d → ℤ)) (v : (d → ℤ) → EuclideanSpace ℂ ι)
    (x : UnitAddTorus d) : polynomial P v x = ∑ q ∈ P, mFourier q x • v q := by
  simp only [polynomial, ContinuousMap.sum_apply, ContinuousMap.coe_mk]

theorem exists_polynomial_approximation (f : C(UnitAddTorus d, EuclideanSpace ℂ ι))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finset (d → ℤ), ∃ v : (d → ℤ) → EuclideanSpace ℂ ι,
      ‖f - polynomial P v‖ < ε := by
  classical
  let δ := ε / ((Fintype.card ι : ℝ) + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have happrox (i : ι) := exists_scalar_approximation
    (⟨fun x ↦ f x i, (PiLp.continuous_apply 2 _ i).comp f.continuous⟩ : C(UnitAddTorus d, ℂ)) hδ
  choose c hc using happrox
  let P := Finset.univ.biUnion (fun i ↦ (c i).support)
  let v : (d → ℤ) → EuclideanSpace ℂ ι := fun q ↦ WithLp.toLp 2 (fun i ↦ c i q)
  have hp (x : UnitAddTorus d) (i : ι) :
      polynomial P v x i = ((c i).sum (fun q a ↦ a • mFourier q)) x := by
    have hsub : (c i).support ⊆ P :=
      Finset.subset_biUnion_of_mem (fun i ↦ (c i).support) (Finset.mem_univ i)
    rw [(c i).sum_of_support_subset hsub (fun q a ↦ a • mFourier q)
      (fun q _ ↦ zero_smul ℂ (mFourier q))]
    simp only [polynomial_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      v, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro q _
    exact mul_comm _ _
  have hb (x : UnitAddTorus d) : ‖f x - polynomial P v x‖ ≤ (Fintype.card ι : ℝ) * δ := by
    let y := f x - polynomial P v x
    have hy : y = ∑ i, PiLp.single 2 i (y i) := by
      ext i
      simp [WithLp.ofLp_sum, Finset.sum_apply]
    calc
      ‖y‖ = ‖∑ i, PiLp.single 2 i (y i)‖ := congrArg norm hy
      _ ≤ ∑ i, ‖(PiLp.single 2 i (y i) : EuclideanSpace ℂ ι)‖ := norm_sum_le _ _
      _ = ∑ i, ‖y i‖ := by simp
      _ ≤ ∑ _i : ι, δ := by
        apply Finset.sum_le_sum
        intro i _
        have h := ((⟨fun x ↦ f x i, (PiLp.continuous_apply 2 _ i).comp f.continuous⟩ :
          C(UnitAddTorus d, ℂ)) - (c i).sum (fun q a ↦ a • mFourier q)).norm_coe_le_norm x
        exact (by simpa only [y, PiLp.sub_apply, hp, ContinuousMap.sub_apply,
          ContinuousMap.coe_mk] using h.trans (hc i).le)
      _ = _ := by simp
  refine ⟨P, v, lt_of_le_of_lt ((ContinuousMap.norm_le _ (by positivity)).mpr hb) ?_⟩
  dsimp [δ]
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith

theorem dense_polynomial_range : Dense (range (fun p :
    Finset (d → ℤ) × ((d → ℤ) → EuclideanSpace ℂ ι) ↦ polynomial p.1 p.2)) := by
  intro f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨P, v, h⟩ := exists_polynomial_approximation f hε
  exact ⟨polynomial P v, ⟨(P, v), rfl⟩, by simpa only [dist_eq_norm] using h⟩

end Mettapedia.Analysis.UnitTorusFourierApproximation
