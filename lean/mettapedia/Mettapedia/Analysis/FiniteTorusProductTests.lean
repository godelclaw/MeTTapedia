import Mettapedia.Analysis.FiniteTorusProduct
import Mettapedia.Analysis.UnitTorusFourierTranslation
import Mettapedia.Analysis.UnitTorusFourierEnergy

/-! Regressions for coordinate splitting, Haar normalization, and Fourier signs. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.FiniteTorusProductTests

open MeasureTheory FiniteTorusProduct UnitTorusFourierTranslation UnitTorusFourierEnergy

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (x : UnitAddTorus (Fin 3)) :
    (splitEquiv 1 2 x).1 0 = x 0 ∧ (splitEquiv 1 2 x).2 1 = x 2 := by
  rw [splitEquiv_apply]
  constructor <;> rfl

example (B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ) (u v : ℂ) :
    (∫ _ : UnitAddTorus (Fin 3), B u v) = B u v := by simp

/-- The selected character has the original output sign, not its conjugate. -/
example (k : Fin 2 → ℤ) (x : UnitAddTorus (Fin 2)) :
    (∫ y : UnitAddTorus (Fin 2),
      UnitAddTorus.mFourier k y * UnitAddTorus.mFourier k (x-y)) = UnitAddTorus.mFourier k x := by
  change (∫ y : UnitAddTorus (Fin 2),
    UnitAddTorus.mFourier k y • (UnitAddTorus.mFourier k) (x-y)) = _
  rw [integral_character_smul_sub]
  simp [mFourierCoeff_character]

example (k p : Fin 2 → ℤ) (h : k ≠ p) (x : UnitAddTorus (Fin 2)) :
    (∫ y : UnitAddTorus (Fin 2),
      UnitAddTorus.mFourier k y * UnitAddTorus.mFourier p (x-y)) = 0 := by
  change (∫ y : UnitAddTorus (Fin 2),
    UnitAddTorus.mFourier k y • (UnitAddTorus.mFourier p) (x-y)) = _
  rw [integral_character_smul_sub]
  simp [mFourierCoeff_character, h]

end Mettapedia.Analysis.FiniteTorusProductTests

#print axioms Mettapedia.Analysis.FiniteTorusProduct.splitEquiv_apply
#print axioms Mettapedia.Analysis.FiniteTorusProduct.measurePreserving_splitEquiv
#print axioms Mettapedia.Analysis.FiniteTorusProduct.integral_split
#print axioms Mettapedia.Analysis.FiniteTorusProduct.integral_bilinear
#print axioms Mettapedia.Analysis.UnitTorusFourierTranslation.mFourier_sub
#print axioms Mettapedia.Analysis.UnitTorusFourierTranslation.integral_character_smul_sub
