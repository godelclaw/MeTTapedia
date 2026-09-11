import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Fourier energy of measurable functions on the unit torus

Parseval and finite-set Bessel bounds are stated for actual measurable
functions, not only their equivalence classes in `Lp`. This interface
also applies to almost-everywhere derivatives of locally Lipschitz fields.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusFourierEnergy

open scoped BigOperators
open MeasureTheory UnitAddTorus

variable {d : Type*} [Fintype d]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem mFourierCoeff_congr_ae {f g : UnitAddTorus d → ℂ} (h : f =ᵐ[volume] g) (q : d → ℤ) :
    mFourierCoeff f q = mFourierCoeff g q := by
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem hasSum_norm_mFourierCoeff_sq (f : UnitAddTorus d → ℂ) (hf : MemLp f 2) :
    HasSum (fun q ↦ ‖mFourierCoeff f q‖ ^ 2) (∫ x, ‖f x‖ ^ 2) := by
  have h := hasSum_sq_mFourierCoeff (hf.toLp f)
  have hc (q : d → ℤ) := mFourierCoeff_congr_ae hf.coeFn_toLp q
  have hi : (∫ x : UnitAddTorus d, ‖hf.toLp f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  simpa only [hc, hi] using h

theorem sum_norm_mFourierCoeff_sq_le (f : UnitAddTorus d → ℂ) (hf : MemLp f 2)
    (P : Finset (d → ℤ)) : (∑ q ∈ P, ‖mFourierCoeff f q‖ ^ 2) ≤ ∫ x, ‖f x‖ ^ 2 := by
  have h := hasSum_norm_mFourierCoeff_sq f hf
  exact sum_le_hasSum P (fun _ _ ↦ sq_nonneg _) h

theorem mFourierCoeff_character (k q : d → ℤ) :
    mFourierCoeff (mFourier k) q = if q = k then 1 else 0 := by
  classical
  have h := orthonormal_iff_ite.mp (orthonormal_mFourier (d := d)) q k
  rw [ContinuousMap.inner_toLp] at h
  simpa only [mFourierCoeff, smul_eq_mul, ← mFourier_neg, mul_comm] using h

end Mettapedia.Analysis.UnitTorusFourierEnergy
