import Mettapedia.Computability.PNP.CruxKpolySupportFullRuleObserved

/-!
# PNP `Kpoly` support/full-rule anchors: uniform sections

Uniform visible-section transfer anchors from observed block outputs to full exact-visible predictor families.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: a uniform visible section is sufficient to transfer
an observed-output finite cover to the full exact-visible predictor family. -/
theorem kpolyCoverage_anchor_uniformVisibleSection_transfers_observed_cover
    {Z : Type v} {Block Index : Type v} {k N : ℕ}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec : T.HasUniformVisibleSection sec)
    (hcover : T.outputFamily.FinitePredictorCover N) :
    T.predictorFamily.FinitePredictorCover N :=
  T.predictorFamily_finitePredictorCover_of_outputFamily_finitePredictorCover
    hsec hcover

/-- Route-coverage anchor: in the support-full-rule construction, a uniform
visible section really does lift the observed block truth-table cover to the
full exact-visible predictor family. -/
theorem kpolyCoverage_anchor_supportFullRule_finitePredictorCover_card_of_uniformVisibleSection
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
      (2 ^ Fintype.card Block) :=
  supportFullRule_predictorFamily_finitePredictorCover_card_of_uniformVisibleSection
    (Z := Z) (k := k) (Block := Block) visibleOf hsec

/-- Route-coverage anchor: under the same uniform visible section, the
observed-output bit budget lifts to a clocked finite-learning payload for the
full exact-visible family at block cardinality. -/
theorem kpolyCoverage_anchor_supportFullRule_clockedPayload_card_of_uniformVisibleSection
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k clock : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    ClockedKpolyFiniteLearningPayload
      (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily
      (Fintype.card Block) clock :=
  supportFullRule_clockedKpolyFiniteLearningPayload_card_of_uniformVisibleSection
    (Z := Z) (k := k) (Block := Block) visibleOf hsec

/-- Route-coverage anchor: in the support-full-rule construction, a uniform
visible section forces the actual block support to be at least as large as the
full exact-visible surface. -/
theorem kpolyCoverage_anchor_supportFullRule_uniformSection_forces_surfaceCard_le_supportCard
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ Fintype.card Block :=
  supportFullRule_surfaceCard_le_blockCard_of_uniformVisibleSection visibleOf hsec

/-- Route-coverage anchor: therefore finite observed support cannot repair the
observed-output bridge when the support has smaller cardinality than the full
exact-visible surface. -/
theorem kpolyCoverage_anchor_supportFullRule_no_uniformSection_below_surfaceCard
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ sec : ExactVisiblePostSwitchSurface Z k → Block,
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec :=
  supportFullRule_not_hasUniformVisibleSection_of_card_lt_surfaceCard visibleOf hcard


end Mettapedia.Computability.PNP
