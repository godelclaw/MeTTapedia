import Mettapedia.Analysis.UnitTorusProductTransport

/-! # Integrating periodic pairs in endpoint-separation coordinates -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusPairIntegration

open MeasureTheory
variable {d : Type*} [Fintype d]
local notation "T" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

theorem integral_pair_eq_separation (f : T → T → ℝ) (hf : Continuous f.uncurry) :
    (∫ x : T, ∫ y : T, f x y) = ∫ h : T, ∫ x : T, f x (x - h) := by
  have hc : Continuous (fun p : T × T ↦ f p.1 (p.1 - p.2)) :=
    hf.comp (continuous_fst.prodMk (continuous_fst.sub continuous_snd))
  calc
    _ = ∫ x : T, ∫ h : T, f x (x - h) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_sub_left_eq_self (f x) (volume : Measure T) x).symm
    _ = _ := integral_integral_swap
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

end Mettapedia.Analysis.UnitTorusPairIntegration
