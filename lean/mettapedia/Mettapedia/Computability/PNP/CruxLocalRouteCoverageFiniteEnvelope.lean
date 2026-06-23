import Mettapedia.Computability.PNP.ClockedKpolyGapAssessment
import Mettapedia.Computability.PNP.PNPv13ACCEIEnvelope

/-!
# PNP local route coverage: finite-kernel and envelope anchors

Finite-learning kernel coverage and ACCEI/PNLD envelope-product route anchors
for the local PNP crux packet.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- The broad packet's clocked finite-uniform kernel entry is covered by the
proved equivalence between the bundled clocked finite-learning payload and a
finite predictor-image cover.  This is only the abstract counting kernel, not
the manuscript-specific small-image theorem. -/
def ClockedFiniteUniformKernelCoverage : Prop :=
  ∀ {Z : Type} [Fintype Z] {k s clock : ℕ} {Index : Type}
    {G : ExactVisibleSwitchedFamily Z k Index},
    ClockedKpolyFiniteLearningPayload G s clock ↔
      G.FinitePredictorCover (2 ^ s)

@[simp] theorem clockedFiniteUniformKernelCoverage :
    ClockedFiniteUniformKernelCoverage := by
  intro Z _FintypeZ k s clock Index G
  exact clockedKpolyFiniteLearningPayload_iff_finitePredictorCover

/-- The v13 ACCEI/PNLD envelope-product ledger entry is covered only at the
finite skeleton level: finite Markov pruning bounds bad coordinates by total
envelope budget, lower-bounds the pruned good-coordinate count by the finite
Markov loss, records a two-coordinate sharpness example for that loss, any
sequential one-step rate proof implies the matching tower-product count bound,
and every product-bound violation localizes to one failed prefix rate step. -/
def V13ACCEIEnvelopeProductCoverage : Prop :=
  (∀ {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ),
      (∑ i, η i) ≤ budget →
        acceiBadCount ι η threshold * (threshold + 1) ≤ budget) ∧
    (∀ {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ),
      (∑ i, η i) ≤ budget →
        Fintype.card ι - budget / (threshold + 1) ≤
          acceiGoodCount ι η threshold) ∧
    (∀ {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ),
      (∑ i, η i) ≤ budget →
        budget / (threshold + 1) < Fintype.card ι →
          ∃ i : ι, η i ≤ threshold) ∧
    (∀ threshold : ℕ,
      acceiBadCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold *
          (threshold + 1) =
        ∑ b : Bool, oneGoodOneBadACCEIEnvelope threshold b) ∧
    (∀ threshold : ℕ,
      Fintype.card Bool - (threshold + 1) / (threshold + 1) =
          acceiGoodCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold ∧
        ¬ ∀ b : Bool, oneGoodOneBadACCEIEnvelope threshold b ≤ threshold) ∧
    (∀ {Ω : Type u} [Fintype Ω]
      (hist rest : List (FiniteEvent Ω)) (numerator denominator : ℕ),
        SequentialRateAdmissibleFrom hist rest numerator denominator →
          denominator ^ rest.length *
              finiteHistoryCount Ω (hist ++ rest) ≤
            numerator ^ rest.length * finiteHistoryCount Ω hist) ∧
    (∀ {Ω : Type u} [Fintype Ω]
      {hist rest : List (FiniteEvent Ω)} {numerator denominator : ℕ},
        ¬ (denominator ^ rest.length *
              finiteHistoryCount Ω (hist ++ rest) ≤
            numerator ^ rest.length * finiteHistoryCount Ω hist) →
          ¬ SequentialRateAdmissibleFrom hist rest numerator denominator) ∧
      ∀ {Ω : Type u} [Fintype Ω]
        {hist events : List (FiniteEvent Ω)} {numerator denominator : ℕ},
          ¬ (denominator ^ events.length *
                finiteHistoryCount Ω (hist ++ events) ≤
              numerator ^ events.length * finiteHistoryCount Ω hist) →
            ∃ pre E suffix,
              events = pre ++ E :: suffix ∧
                ¬ PrefixRateStep (hist ++ pre) E numerator denominator

@[simp] theorem v13ACCEIEnvelopeProductCoverage :
    V13ACCEIEnvelopeProductCoverage := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ι _Fintypeι η threshold budget hbudget
    exact acceiBadCount_mul_succ_threshold_le_of_sum_le
      η threshold budget hbudget
  · intro ι _Fintypeι η threshold budget hbudget
    exact
      card_sub_budget_div_succ_threshold_le_acceiGoodCount_of_sum_le
        η threshold budget hbudget
  · intro ι _Fintypeι η threshold budget hbudget hloss
    exact
      exists_accei_good_of_budget_div_succ_threshold_lt_card
        η threshold budget hbudget hloss
  · intro threshold
    exact oneGoodOneBadACCEIEnvelope_markov_badCount_sharp threshold
  · intro threshold
    exact
      ⟨oneGoodOneBadACCEIEnvelope_good_lower_bound_sharp threshold,
        oneGoodOneBadACCEIEnvelope_not_all_good threshold⟩
  · intro Ω _FintypeΩ hist rest numerator denominator hseq
    exact finiteHistory_product_bound_of_sequentialRateFrom
      hist rest numerator denominator hseq
  · intro Ω _FintypeΩ hist rest numerator denominator hbad
    exact not_sequentialRateAdmissibleFrom_of_product_bound_violation hbad
  · intro Ω _FintypeΩ hist events numerator denominator hbad
    exact
      exists_failed_prefixRateStep_at_append_cons_of_product_bound_violation
        hbad

end Mettapedia.Computability.PNP
