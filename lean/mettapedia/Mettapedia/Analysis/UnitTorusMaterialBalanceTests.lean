import Mettapedia.Analysis.UnitTorusProductTransport

/-! Regression tests for signed mean transport, including a nonsmooth time interface. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusMaterialBalanceTests

open MeasureTheory UnitTorusWeakDerivative UnitTorusMaterialBalance UnitTorusProductTransport

local notation "T6" => UnitAddTorus (Fin 3 ⊕ Fin 3)
local notation "X6" => Fin 3 ⊕ Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem materialRate_time (v : T6 → X6) (t : ℝ) (x : T6) :
    scalarMaterialRate (fun s _ ↦ s) v t x = 1 := by
  exact ((hasDerivAt_id (0 : ℝ)).const_add t).deriv

theorem productVelocity_divergence_const (v w : Fin 3 → ℝ) (x : T6) :
    coordinateDivergence (fun j y ↦ pairVelocity (fun _ ↦ v) (fun _ ↦ w) y j) x = 0 := by
  rw [coordinateDivergence_pairVelocity]
  simp [coordinateDivergence, shiftRate]

/-- A corner at time zero is admissible; the signed endpoint change is zero. -/
theorem integral_materialRate_abs_zero :
    (∫ t in (-1 : ℝ)..1, ∫ x : T6,
      scalarMaterialRate (fun s _ ↦ |s|) (fun _ ↦ (0 : X6)) t x) = 0 := by
  have hl : LocallyLipschitz (fun z : ℝ × X6 ↦ |z.1|) := by
    have hn : LocallyLipschitz (fun z : ℝ × X6 ↦ ‖z.1‖) :=
      (lipschitzWith_one_norm.comp LipschitzWith.prod_fst).locallyLipschitz
    simpa only [Real.norm_eq_abs] using hn
  have h := intervalIntegral_materialRate_eq
    (fun (s : ℝ) (_ : T6) ↦ |s|) (fun _ _ ↦ (0 : X6))
    (by fun_prop) (fun _ ↦ continuous_const) hl
    (fun _ _ ↦ LocallyLipschitz.const 0)
    (fun _ ↦ Filter.Eventually.of_forall (fun _ ↦ by simp [coordinateDivergence, shiftRate]))
    (-1) 1
  simpa using h.2

end Mettapedia.Analysis.UnitTorusMaterialBalanceTests
