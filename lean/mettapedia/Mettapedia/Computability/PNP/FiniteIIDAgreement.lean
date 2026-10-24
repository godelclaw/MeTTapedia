import Mettapedia.Computability.PNP.FiniteConsistencyBound
import Mettapedia.ProbabilityTheory.FiniteEventMass
import Mathlib.Data.ENNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Independent finite-sample agreement

A sample has the product of its point weights. Agreement on every sample
point therefore has mass `agreementMass ^ m`, by the shared finite-event
product law. The subtype definitions below remain independent of that law.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal BigOperators
open Mettapedia.ProbabilityTheory


universe u v


variable {Input : Type u} {Output : Type v}
variable [Fintype Input] [DecidableEq Output]

/-- The total input mass on which `predict` agrees with `target`. -/
noncomputable def agreementMass
    (μ : PMF Input) (target predict : Input → Output) : ℝ≥0∞ :=
  ∑ a : AgreementPoints target predict, μ a.1

/-- The product mass of one length-`m` point sample under independent draws from `μ`. -/
noncomputable def sampleMass
    (μ : PMF Input) {m : ℕ} (sample : PointSample Input m) : ℝ≥0∞ :=
  ∏ i, μ (sample i)

/-- The total mass of length-`m` samples on which `predict` agrees with `target`
at every sampled point. -/
noncomputable def consistentSampleMass
    (μ : PMF Input) (target predict : Input → Output) (m : ℕ) : ℝ≥0∞ :=
  ∑ sample : ConsistentSamples target predict m, sampleMass μ sample.1

theorem consistentSampleMass_eq_agreementMass_pow
    (μ : PMF Input) (target predict : Input → Output) (m : ℕ) :
    consistentSampleMass μ target predict m = agreementMass μ target predict ^ m := by
  classical
  unfold consistentSampleMass agreementMass
  rw [← FiniteEventMass.mass_subtype (sampleMass μ) (AgreesWithTarget target predict)
    (subtypeFintype := consistentSamplesFintype target predict m),
    ← FiniteEventMass.mass_subtype (μ : Input → ℝ≥0∞) (fun x => predict x = target x)
    (subtypeFintype := agreementPointsFintype target predict)]
  exact (FiniteEventMass.congr _
    (fun sample => decide_eq_decide.mpr (by simp [AgreesWithTarget]))).trans
    (FiniteEventMass.product_event (μ : Input → ℝ≥0∞) (fun x => decide (predict x = target x)) m)

theorem consistentSampleMass_le_pow_of_agreementMass_le
    (μ : PMF Input) (target predict : Input → Output) (m : ℕ) {q : ℝ≥0∞}
    (hq : agreementMass μ target predict ≤ q) :
    consistentSampleMass μ target predict m ≤ q ^ m := by
  rw [consistentSampleMass_eq_agreementMass_pow]
  exact (pow_left_mono m) hq

end Mettapedia.Computability.PNP
