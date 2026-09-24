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

/-- Integration by parts for actual continuous translation derivatives. -/
theorem integral_rate_mul (f g df dg : T → ℝ) (s : ℝ → T)
    (hf : Continuous f) (hg : Continuous g) (hdf : Continuous df) (hdg : Continuous dg)
    (hs : Continuous s) (hs0 : s 0 = 0)
    (hf' : ∀ x h, HasDerivAt (fun t ↦ f (x + s t)) (df (x + s h)) h)
    (hg' : ∀ x h, HasDerivAt (fun t ↦ g (x + s t)) (dg (x + s h)) h) :
    (∫ x : T, df x * g x) = -(∫ x : T, f x * dg x) := by
  have hz := integral_rate_eq_zero (fun x ↦ f x * g x)
    (fun x ↦ df x * g x + f x * dg x) s (hf.mul hg)
    ((hdf.mul hg).add (hf.mul hdg)) hs hs0 (fun x h ↦ (hf' x h).mul (hg' x h))
  have hi₁ : Integrable (fun x : T ↦ df x * g x) :=
    (hdf.mul hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi₂ : Integrable (fun x : T ↦ f x * dg x) :=
    (hf.mul hdg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_add hi₁ hi₂] at hz
  linarith

end Mettapedia.Analysis.UnitTorusContinuousRate
