import Mettapedia.MeasureTheory.AdditiveValuation
import Mathlib.MeasureTheory.Group.Integral

/-!
# Integration and translation invariance of constructed measures

Measurable-event invariance gives left invariance. Haar measure additionally
requires finiteness on compact sets and positivity on nonempty open sets.
Integration uses the resulting Mathlib measure without extra symmetry laws.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Mettapedia.MeasureTheory.MeasurableContent

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integrable_toMeasure_iff (c : MeasurableContent Ω) (hc : SigmaAdditive c)
    (f : Ω → ℝ) (hf : Measurable f) :
    Integrable f (toMeasure c hc) ↔ (∫⁻ x, ‖f x‖ₑ ∂toMeasure c hc) < ∞ :=
  ⟨fun h => h.2, fun h => ⟨hf.aestronglyMeasurable, h⟩⟩

/-- Measurable-event invariance gives left invariance of the extension. -/
@[to_additive]
theorem toMeasure_isMulLeftInvariant {G : Type*} [Mul G] [MeasurableSpace G]
    [MeasurableMul G] (c : MeasurableContent G) (hc : SigmaAdditive c)
    (invariant : ∀ g s, MeasurableSet s → c ((g * ·) ⁻¹' s) = c s) :
    Measure.IsMulLeftInvariant (toMeasure c hc) := by
  refine ⟨fun g => Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_const_mul g) hs,
    toMeasure_apply _ _ (hs.preimage (measurable_const_mul g)), toMeasure_apply _ _ hs]
  exact invariant g s hs

@[to_additive]
theorem integral_mul_left_toMeasure {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (c : MeasurableContent G) (hc : SigmaAdditive c)
    (invariant : ∀ g s, MeasurableSet s → c ((g * ·) ⁻¹' s) = c s)
    (f : G → ℝ) (g : G) :
    ∫ x, f (g * x) ∂toMeasure c hc = ∫ x, f x ∂toMeasure c hc := by
  let _ := toMeasure_isMulLeftInvariant c hc invariant
  exact integral_mul_left_eq_self f g

theorem lintegral_iSup_toMeasure (c : MeasurableContent Ω) (hc : SigmaAdditive c)
    (f : ℕ → Ω → ℝ≥0∞) (hf : ∀ n, Measurable (f n))
    (hm : ∀ x, Monotone (fun n => f n x)) :
    (∫⁻ x, ⨆ n, f n x ∂toMeasure c hc) = ⨆ n, ∫⁻ x, f n x ∂toMeasure c hc :=
  lintegral_iSup hf (fun _ _ h x => hm x h)

end Mettapedia.MeasureTheory.MeasurableContent
