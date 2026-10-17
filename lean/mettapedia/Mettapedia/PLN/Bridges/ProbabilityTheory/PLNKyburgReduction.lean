import Mettapedia.PLN.Evidence.BinaryEvidence
import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
import Mettapedia.ProbabilityTheory.HigherOrderProbability.KyburgFlattening
import Mettapedia.ProbabilityTheory.HigherOrderProbability.GiryMonad
import Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection

/-!
# PLN evidence and Kyburg flattening

Binary evidence `(n⁺, n⁻)` with a prior context `(α₀, β₀)` reads out the
posterior mean of a Beta distribution (`strengthWith_eq_beta_posterior_meanENN`),
and revision adds counts, which is the conjugate Beta update
(`EvidenceBeta.hplus_is_beta_aggregation`,
`EvidenceBeta.evidence_aggregation_is_conjugate_update`).  On the higher-order
side, a parametrized distribution flattens to its marginal
(`HigherOrderProbability.kyburg_flattening`, `flatten_is_marginal`,
`kyburg_no_advantage`, and the monad laws in `GiryMonad`), so a second-order
distribution gives no decision advantage over its flattening (Kyburg,
*Higher Order Probabilities and Intervals*).

`evidenceAggregation_and_kyburgFlattening` states both facts together.
-/

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.PLNKyburgReduction

open scoped ENNReal
open MeasureTheory
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Evidence.EvidenceClass (BinaryContext)
open Mettapedia.ProbabilityTheory.HigherOrderProbability (ParametrizedDistribution)

/-! ## BinaryEvidence-side bridge lemmas -/

/-- Context-aware PLN strength is exactly a Beta posterior-mean form over
shifted pseudo-count coordinates in `ℝ≥0∞`. -/
theorem strengthWith_eq_beta_posterior_meanENN (e : BinaryEvidence) (ctx : BinaryContext) :
    Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.strengthWith ctx e =
      (ctx.α₀ + e.pos) / ((ctx.α₀ + e.pos) + (ctx.β₀ + e.neg)) := by
  simp [Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.strengthWith, add_comm, add_left_comm]

/-- BinaryEvidence determines the shifted Beta pseudo-count coordinates used by
`strengthWith`; this is the compact sufficient-statistic encoding view. -/
theorem evidence_encodes_beta_parameters (e : BinaryEvidence) (ctx : BinaryContext) :
    ∃ α β : ℝ≥0∞,
      α = ctx.α₀ + e.pos ∧
      β = ctx.β₀ + e.neg ∧
      Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.strengthWith ctx e = α / (α + β) := by
  refine ⟨ctx.α₀ + e.pos, ctx.β₀ + e.neg, rfl, rfl, ?_⟩
  simpa [add_assoc, add_comm, add_left_comm] using
    strengthWith_eq_beta_posterior_meanENN (e := e) (ctx := ctx)

/-! ## Concrete Chapter-7 worked fixture -/

/-- Concrete worked example (Chapter 7):
with uniform Beta prior `(α₀,β₀)=(1,1)` and observed evidence `(n⁺,n⁻)=(3,1)`,
the context-aware PLN strength is exactly the corresponding posterior-mean ratio. -/
theorem uniformPrior_strength_threePositive_oneNegative :
    Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.strengthWith
        Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform
        ({ pos := (3 : ℝ≥0∞), neg := (1 : ℝ≥0∞) } : BinaryEvidence) =
      ((1 : ℝ≥0∞) + 3) / (((1 : ℝ≥0∞) + 3) + ((1 : ℝ≥0∞) + 1)) := by
  simpa [Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform] using
    strengthWith_eq_beta_posterior_meanENN
      ({ pos := (3 : ℝ≥0∞), neg := (1 : ℝ≥0∞) } : BinaryEvidence)
      Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform

/-! ## Chapter-7-facing aggregate statement -/

/-- Compact chapter-facing bundle: PLN evidence aggregation + Kyburg flattening
decision-equivalence are both available as proved endpoints in the core stack. -/
theorem evidenceAggregation_and_kyburgFlattening :
    (∀ e₁ e₂ : BinaryEvidence,
      (e₁ + e₂).pos = e₁.pos + e₂.pos ∧ (e₁ + e₂).neg = e₁.neg + e₂.neg) ∧
    (∀ {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
        (pd : ParametrizedDistribution Θ X) (A : Set X),
        MeasurableSet A →
          (Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution.flatten pd) A =
            ∫⁻ θ, (pd.kernel θ) A ∂pd.mixingMeasure) := by
  constructor
  · intro e₁ e₂
    exact Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.hplus_is_beta_aggregation e₁ e₂
  · intro Θ X _ _ pd A hA
    simpa using Mettapedia.ProbabilityTheory.HigherOrderProbability.kyburg_flattening pd A hA

end Mettapedia.PLN.Bridges.ProbabilityTheory.PLNKyburgReduction
