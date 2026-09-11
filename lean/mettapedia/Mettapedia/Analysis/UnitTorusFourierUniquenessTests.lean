import Mettapedia.Analysis.UnitTorusFourierUniqueness

/-! Pointwise uniqueness and exact finite reconstruction tests. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusFourierUniquenessTests

open MeasureTheory UnitAddTorus UnitTorusFourierUniqueness

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example {d E : Type*} [Fintype d] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (f : C(UnitAddTorus d, E)) (h : ∀ q, mFourierCoeff f q = 0) :
    f = 0 := by
  apply eq_of_mFourierCoeff_eq
  intro q
  change mFourierCoeff f q = UnitTorusContinuousFourier.coefficientCLM q 0
  simpa only [map_zero] using h q

example (q : Fin 2 → ℤ) (a : (Fin 2 → ℤ) → ℂ) :
    polynomial {q} a (0 : UnitAddTorus (Fin 2)) = a q := by
  simp [mFourier]

example (q p : Fin 2 → ℤ) (h : q ≠ p) (a : (Fin 2 → ℤ) → ℂ) :
    mFourierCoeff (polynomial {p} a) q = 0 := by
  simp [mFourierCoeff_polynomial, h]

end Mettapedia.Analysis.UnitTorusFourierUniquenessTests

#print axioms Mettapedia.Analysis.UnitTorusFourierUniqueness.scalar_eq_of_mFourierCoeff_eq
#print axioms Mettapedia.Analysis.UnitTorusFourierUniqueness.mFourierCoeff_map
#print axioms Mettapedia.Analysis.UnitTorusFourierUniqueness.eq_of_mFourierCoeff_eq
#print axioms Mettapedia.Analysis.UnitTorusFourierUniqueness.mFourierCoeff_polynomial
#print axioms Mettapedia.Analysis.UnitTorusFourierUniqueness.eq_polynomial
