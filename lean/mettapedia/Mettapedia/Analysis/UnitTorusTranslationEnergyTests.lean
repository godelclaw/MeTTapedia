import Mettapedia.Analysis.UnitTorusTranslationEnergy

/-! Wrapped representatives, Fourier phase, and constant translation regressions. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusTranslationEnergyTests

open MeasureTheory UnitAddTorus UnitTorusTranslationEnergy UnitTorusFourierEnergy

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- An arbitrary real representative cannot replace wrapped distance. -/
example : ¬ ∀ r : ℝ, |r| ≤ ‖(r : UnitAddCircle)‖ := by
  intro h
  have h1 := h 1
  norm_num [AddCircle.coe_period] at h1

example : ‖((3 / 4 : ℝ) : UnitAddCircle)‖ = 1 / 4 := by
  have he : (3 / 4 : ℝ) = -1 / 4 + 1 := by norm_num
  rw [he, AddCircle.coe_add]
  simp only [AddCircle.coe_period, add_zero]
  have h := (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero (x := -1 / 4)).mpr (by norm_num)
  norm_num at h ⊢
  exact h

/-- Translation multiplies a nonzero Fourier coefficient by its actual phase. -/
example {d : Type*} [Fintype d] (k q : d → ℤ) (a : UnitAddTorus d) :
    mFourierCoeff (fun x ↦ mFourier k (x + a)) q = if q = k then mFourier k a else 0 := by
  classical
  rw [mFourierCoeff_translate, mFourierCoeff_character]
  split_ifs with h
  · simp [h]
  · simp

example {d : Type*} [Fintype d] (a : UnitAddTorus d) (c : ℂ) :
    (∫ _x : UnitAddTorus d, ‖c - c‖ ^ 2) ≤ (Fintype.card d : ℝ) * ‖a‖ ^ 2 * 0 := by simp

example {d : Type*} [Fintype d] (a : UnitAddTorus d) :
    ∃ r : d → ℝ, (fun j ↦ (r j : UnitAddCircle)) = a ∧ ‖r‖ = ‖a‖ :=
  exists_norm_preserving_lift a

end Mettapedia.Analysis.UnitTorusTranslationEnergyTests

#print axioms Mettapedia.Analysis.UnitTorusTranslationEnergy.exists_norm_preserving_lift
#print axioms Mettapedia.Analysis.UnitTorusTranslationEnergy.mFourier_lift
#print axioms Mettapedia.Analysis.UnitTorusTranslationEnergy.norm_mFourier_sub_one_sq_le
#print axioms Mettapedia.Analysis.UnitTorusTranslationEnergy.mFourierCoeff_translate
#print axioms Mettapedia.Analysis.UnitTorusTranslationEnergy.mFourierCoeff_sub
#print axioms Mettapedia.Analysis.UnitTorusTranslationEnergy.integral_norm_translate_sub_sq_le
