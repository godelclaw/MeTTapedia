import Mettapedia.Analysis.UnitTorusFourierApproximation
import Mathlib.Tactic.NormNum

/-! Retained and omitted Fourier modes, including the physical omitted-mode error. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusFourierTests

open scoped BigOperators
open MeasureTheory UnitAddTorus UnitTorusFourierEnergy UnitTorusFourierApproximation

local notation "T1" => UnitAddTorus (Fin 1)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example : mFourierCoeff (mFourier (fun _ : Fin 1 ↦ 1)) (fun _ ↦ 1) = 1 := by
  simp [mFourierCoeff_character]

example : mFourierCoeff (mFourier (fun _ : Fin 1 ↦ 1)) (fun _ ↦ -1) = 0 := by
  rw [mFourierCoeff_character, if_neg]
  intro h
  have h0 := congrFun h 0
  norm_num at h0

example (k : Fin 1 → ℤ) : projection (mFourier k) {k} = mFourier k := by
  simp [projection, mFourierCoeff_character]

/-- Omitting a unit character leaves error one, not zero. -/
example : (∫ x : T1,
    ‖projection (mFourier (fun _ : Fin 1 ↦ 1)) ∅ x - mFourier (fun _ ↦ 1) x‖ ^ 2) = 1 := by
  simp [projection, mFourier, fourier_apply]

end Mettapedia.Analysis.UnitTorusFourierTests

#print axioms Mettapedia.Analysis.UnitTorusFourierEnergy.mFourierCoeff_congr_ae
#print axioms Mettapedia.Analysis.UnitTorusFourierEnergy.hasSum_norm_mFourierCoeff_sq
#print axioms Mettapedia.Analysis.UnitTorusFourierEnergy.sum_norm_mFourierCoeff_sq_le
#print axioms Mettapedia.Analysis.UnitTorusFourierEnergy.mFourierCoeff_character
#print axioms Mettapedia.Analysis.UnitTorusFourierApproximation.norm_toLp_sq
#print axioms Mettapedia.Analysis.UnitTorusFourierApproximation.toLp_projection
#print axioms Mettapedia.Analysis.UnitTorusFourierApproximation.integral_projection_error_eq
#print axioms Mettapedia.Analysis.UnitTorusFourierApproximation.tendsto_integral_projection_error
#print axioms Mettapedia.Analysis.UnitTorusFourierApproximation.exists_sum_integral_projection_error_lt
