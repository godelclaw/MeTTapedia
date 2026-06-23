import Mettapedia.Computability.PNP.CruxKpolySupportFullRuleUniformSection

/-!
# CruxSynthesisRegressionKpolySupportRuleUniformSection

Uniform visible-section transfer and cardinality regressions.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_uniform_visible_section_transfers_observed_cover_regression
    {Z : Type v} {Block Index : Type v} {k N : ℕ}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec : T.HasUniformVisibleSection sec)
    (hcover : T.outputFamily.FinitePredictorCover N) :
    T.predictorFamily.FinitePredictorCover N := by
  exact
    kpolyCoverage_anchor_uniformVisibleSection_transfers_observed_cover
      T hsec hcover

theorem kpoly_anchor_support_full_rule_uniform_section_finite_cover_regression
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
      (2 ^ Fintype.card Block) := by
  exact
    kpolyCoverage_anchor_supportFullRule_finitePredictorCover_card_of_uniformVisibleSection
      visibleOf hsec

theorem kpoly_anchor_support_full_rule_uniform_section_clocked_payload_regression
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k clock : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    ClockedKpolyFiniteLearningPayload
      (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily
      (Fintype.card Block) clock := by
  exact
    kpolyCoverage_anchor_supportFullRule_clockedPayload_card_of_uniformVisibleSection
      visibleOf hsec

theorem kpoly_anchor_support_full_rule_uniform_section_forces_card_regression
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ Fintype.card Block := by
  exact
    kpolyCoverage_anchor_supportFullRule_uniformSection_forces_surfaceCard_le_supportCard
      visibleOf hsec

theorem kpoly_anchor_support_full_rule_no_uniform_section_regression
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ sec : ExactVisiblePostSwitchSurface Z k → Block,
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec := by
  exact
    kpolyCoverage_anchor_supportFullRule_no_uniformSection_below_surfaceCard
      visibleOf hcard

end Mettapedia.Computability.PNP.CruxSynthesisRegression
