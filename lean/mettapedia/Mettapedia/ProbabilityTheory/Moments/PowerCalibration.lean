import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-!
# Calibration by a finite power moment

On a probability space, a finite power moment strictly greater than one
identifies its positive exponent among all moments of the same observable.
This follows from comparison of probability-space `Lᵖ` norms; no special-function
representation or strict convexity assumption on the observable is needed.
-/

namespace Mettapedia.ProbabilityTheory.Moments

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  {μ : Measure Ω} {f : Ω → E}

/-- The nonnegative extended power moment, retaining possible divergence. -/
def powerMoment (μ : Measure Ω) (f : Ω → E) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ‖f x‖ₑ ^ p ∂μ

/-- Probability normalization bounds the smaller moment by a power of the larger. -/
theorem powerMoment_le_rpow [IsProbabilityMeasure μ]
    (hf : AEStronglyMeasurable f μ) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    powerMoment μ f p ≤ powerMoment μ f q ^ (p / q) := by
  have h := eLpNorm'_le_eLpNorm'_of_exponent_le hp hpq μ hf
  have hpow := (ENNReal.rpow_le_rpow_iff hp).2 h
  simpa only [eLpNorm'_eq_lintegral_enorm, ← ENNReal.rpow_mul,
    one_div_mul_cancel hp.ne', ENNReal.rpow_one, one_div_mul_eq_div,
    powerMoment] using hpow

/-- A moment above one is strictly smaller than every moment at a larger exponent. -/
theorem powerMoment_lt_of_lt_exponent [IsProbabilityMeasure μ]
    (hf : AEStronglyMeasurable f μ) {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (hlarge : 1 < powerMoment μ f q) (hfinite : powerMoment μ f q ≠ ∞) :
    powerMoment μ f p < powerMoment μ f q := by
  have hratio : p / q < 1 := (div_lt_one (hp.trans hpq)).2 hpq
  exact (powerMoment_le_rpow hf hp hpq.le).trans_lt (by
    simpa only [ENNReal.rpow_one] using
      ENNReal.rpow_lt_rpow_of_exponent_lt hlarge hfinite hratio)

/-- Equal finite moments above one have equal positive exponents. -/
theorem powerMoment_eq_iff [IsProbabilityMeasure μ]
    (hf : AEStronglyMeasurable f μ) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hlarge : 1 < powerMoment μ f q) (hfinite : powerMoment μ f q ≠ ∞) :
    powerMoment μ f p = powerMoment μ f q ↔ p = q := by
  refine ⟨fun heq => ?_, fun h => h ▸ rfl⟩
  rcases lt_trichotomy p q with h | h | h
  · exact False.elim ((ne_of_lt (powerMoment_lt_of_lt_exponent hf hp h hlarge hfinite)) heq)
  · exact h
  · have hlarge' : 1 < powerMoment μ f p := heq ▸ hlarge
    have hfinite' : powerMoment μ f p ≠ ∞ := heq ▸ hfinite
    exact False.elim ((ne_of_lt (powerMoment_lt_of_lt_exponent hf hq h hlarge' hfinite')) heq.symm)

/-- Unit observables cannot identify an exponent: the strict moment bound matters. -/
theorem unit_moment (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ℝ) :
    powerMoment μ (fun _ => (1 : ℝ)) p = 1 := by
  simp [powerMoment]

/-- Without probability normalization, even a moment of two does not identify an exponent. -/
theorem unnormalized_unit_moment (p : ℝ) :
    powerMoment (2 • Measure.dirac ()) (fun _ : Unit => (1 : ℝ)) p = 2 := by
  simp [powerMoment]

end

end Mettapedia.ProbabilityTheory.Moments
