import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Fourier coefficient selection by a translated character integral. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusFourierTranslation

open MeasureTheory

variable {d E : Type*} [Fintype d] [NormedAddCommGroup E] [NormedSpace ℂ E]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem mFourier_sub (k : d → ℤ) (x y : UnitAddTorus d) :
    UnitAddTorus.mFourier k (x - y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.sub_apply,
    fourier_apply, zsmul_sub]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Circle.coe_mul, ← AddCircle.toCircle_add]
  congr 2
  rw [Pi.neg_apply, neg_zsmul, sub_eq_add_neg]

theorem integral_character_smul_sub (f : UnitAddTorus d → E)
    (k : d → ℤ) (x : UnitAddTorus d) :
    (∫ y : UnitAddTorus d, UnitAddTorus.mFourier k y • f (x - y)) =
      UnitAddTorus.mFourier k x • UnitAddTorus.mFourierCoeff f k := by
  rw [← integral_sub_left_eq_self (fun y ↦ UnitAddTorus.mFourier k y • f (x - y)) volume x]
  simp only [sub_sub_cancel, mFourier_sub, mul_smul, integral_smul, UnitAddTorus.mFourierCoeff]

end Mettapedia.Analysis.UnitTorusFourierTranslation
