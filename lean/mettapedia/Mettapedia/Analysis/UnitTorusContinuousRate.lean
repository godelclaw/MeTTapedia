import Mettapedia.Analysis.UnitTorusWeakDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-! # Zero mean of an actual continuous periodic translation derivative -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusContinuousRate

open scoped Topology NNReal
open MeasureTheory UnitTorusWeakDerivative

variable {d : Type*} [Fintype d]
local notation "T" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_rate_eq_zero (f rate : T → ℝ) (s : ℝ → T)
    (hf : Continuous f) (hr : Continuous rate) (hs : Continuous s) (hs0 : s 0 = 0)
    (hd : ∀ x h, HasDerivAt (fun t ↦ f (x + s t)) (rate (x + s h)) h) :
    (∫ x : T, rate x) = 0 := by
  obtain ⟨x₀, hC⟩ := hr.nnnorm.exists_forall_ge (by simp)
  have hlip (x : T) : LipschitzWith ‖rate x₀‖₊ (fun h ↦ f (x + s h)) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun h ↦ (hd x h).differentiableAt)
    intro h
    rw [(hd x h).deriv]
    exact hC _
  have hzero := (integral_shiftRate_zero f s hf hs Set.univ Filter.univ_mem ‖rate x₀‖₊
    (fun x ↦ (hlip x).lipschitzOnWith)
    (Filter.Eventually.of_forall (fun x ↦ (hd x 0).differentiableAt))).2
  have he : shiftRate f s = rate := by
    funext x
    simpa only [shiftRate, hs0, add_zero] using (hd x 0).deriv
  simpa only [he] using hzero

end Mettapedia.Analysis.UnitTorusContinuousRate
