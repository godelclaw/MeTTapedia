import Mettapedia.Analysis.BilinearTranslatedCoefficient
import Mettapedia.Analysis.GaussianMomentContinuity

/-! Integrability of the two-point root-partition derivative cost. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RootPartitionEnergy

open MeasureTheory BilinearTranslatedCoefficient GaussianPartitionEnergy

variable {A X E ι : Type*} [MeasurableSpace A] [MeasurableSpace X]
variable [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] [CompactSpace X]
variable [AddCommGroup X] [MeasurableAdd₂ X] [MeasurableNeg X]
variable {μ : Measure A} {ν : Measure X} [SFinite μ] [SFinite ν] [ν.IsAddRightInvariant]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι] [Nonempty ι]

theorem integrable_twoPointDerivativeCost (B w : X → ℝ) (P : X → E)
    (dB dP dw : X → ℝ) (hB : Continuous B) (hw : Continuous w) (hP : Continuous P)
    (hdB : Integrable (fun x ↦ dB x ^ 2) ν) (hdP : Integrable (fun x ↦ dP x ^ 2) ν)
    (hdw : Integrable (fun x ↦ dw x ^ 2) ν) (center : ι → E) (tau : ℝ)
    (M : A → ℝ) (hM : Integrable M μ) (a b : A → X) (ha : Measurable a) (hb : Measurable b) :
    Integrable (fun p : A × X ↦ M p.1 *
      (2 * B (p.2 - b p.1) ^ 2 * w (p.2 - b p.1) ^ 3 * w (p.2 - a p.1) ^ 3 *
        (2 * dB (p.2 - a p.1) ^ 2 + B (p.2 - a p.1) ^ 2 / tau ^ 2 * dP (p.2 - a p.1) ^ 2 *
          twoPointDistanceMoment center tau (P (p.2 - a p.1)) (P (p.2 - b p.1))) +
        8 * B (p.2 - b p.1) ^ 2 * B (p.2 - a p.1) ^ 2 * w (p.2 - b p.1) ^ 3 *
          w (p.2 - a p.1) * dw (p.2 - a p.1) ^ 2)) (μ.prod ν) := by
  have hpair : Continuous (fun p : X × X ↦ (P p.1, P p.2)) :=
    (hP.comp continuous_fst).prodMk (hP.comp continuous_snd)
  have hH : Continuous (fun p : X × X ↦ twoPointDistanceMoment center tau (P p.1) (P p.2)) :=
    (continuous_twoPointDistanceMoment center tau).comp
      (f := fun p : X × X ↦ (P p.1, P p.2)) hpair
  let c0 : C(X × X, ℝ) := ⟨fun p ↦ 4 * B p.2 ^ 2 * w p.2 ^ 3 * w p.1 ^ 3, by fun_prop⟩
  let c1 : C(X × X, ℝ) := ⟨fun p ↦ 2 * B p.2 ^ 2 * w p.2 ^ 3 * w p.1 ^ 3 *
    (B p.1 ^ 2 / tau ^ 2) * twoPointDistanceMoment center tau (P p.1) (P p.2), by fun_prop⟩
  let c2 : C(X × X, ℝ) := ⟨fun p ↦ 8 * B p.2 ^ 2 * B p.1 ^ 2 * w p.2 ^ 3 * w p.1, by fun_prop⟩
  have h0 := integrable_weighted_translate_mul_continuous M _ hM hdB a b ha hb c0
  have h1 := integrable_weighted_translate_mul_continuous M _ hM hdP a b ha hb c1
  have h2 := integrable_weighted_translate_mul_continuous M _ hM hdw a b ha hb c2
  apply ((h0.add h1).add h2).congr
  filter_upwards [] with p
  simp only [Pi.add_apply]
  dsimp only [c0, c1, c2, ContinuousMap.coe_mk]
  ring

end Mettapedia.Analysis.RootPartitionEnergy
