import Mettapedia.Analysis.UnitTorusFourierEnergy

/-!
# Finite Fourier projections with vanishing physical L2 error

Finite projections use the actual Fourier coefficients. Their spatial
error tends to zero without assuming absolute summability of the Fourier
series. This is L2 convergence, not pointwise or uniform convergence.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusFourierApproximation

open scoped BigOperators Topology
open MeasureTheory UnitAddTorus Filter

variable {d : Type*} [Fintype d]

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

end Mettapedia.Analysis.UnitTorusFourierApproximation
