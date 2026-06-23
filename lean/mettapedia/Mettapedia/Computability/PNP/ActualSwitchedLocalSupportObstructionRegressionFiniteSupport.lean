import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportTransfer
import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportAdaptive
import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportFullRule
import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportCardinality
import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportOneBlock

/-!
# Finite observed-support regression checks for the actual-local support obstruction
-/

namespace Mettapedia.Computability.PNP

universe v

section FiniteObservedSupport

variable {Z : Type v} {Block : Type*} {k s clock : ℕ}
variable (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)

theorem regression_supportFullRule_surjective :
    Function.Surjective
      (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict := by
  exact supportFullRule_surjective visibleOf

theorem regression_supportFullRule_observed_budget_card
    [Fintype Block] :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.HasBitBudget
      (Fintype.card Block) := by
  exact supportFullRule_outputFamily_hasBitBudget_card visibleOf

theorem regression_supportFullRule_observed_cover_card
    [Fintype Block] :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FinitePredictorCover
      (2 ^ Fintype.card Block) := by
  exact supportFullRule_outputFamily_finitePredictorCover_card visibleOf

theorem regression_supportFullRule_outputFamily_factorsThrough_predictorFamily :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FactorsThrough
      visibleOf (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily := by
  exact supportFullRule_outputFamily_factorsThrough_predictorFamily visibleOf

theorem regression_supportFullRule_off_support_rules_indistinguishable
    (hnot : ¬ Function.Surjective visibleOf) :
    ∃ rule₀ rule₁ : ExactVisibleRule Z k,
      rule₀ ≠ rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₀ ≠
          (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₁ := by
  exact
    supportFullRule_exists_distinct_rules_same_outputFamily_of_not_surjective
      visibleOf hnot

theorem regression_supportFullRule_observed_rule_injective_forces_surjective :
    Function.Injective
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict →
      Function.Surjective visibleOf := by
  exact
    supportFullRule_observedRuleMap_injective_forces_visibleOf_surjective
      visibleOf

theorem regression_supportFullRule_exact_decoder_forces_surjective
    (decode : (Block → Bool) → ExactVisibleRule Z k)
    (hdecode :
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule) :
    Function.Surjective visibleOf := by
  exact
    supportFullRule_exactDecoder_forces_visibleOf_surjective
      visibleOf decode hdecode

theorem regression_supportFullRule_no_exact_decoder_of_not_surjective
    (hnot : ¬ Function.Surjective visibleOf) :
    ¬ ∃ decode : (Block → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule := by
  exact
    supportFullRule_not_exists_exactDecoder_of_not_surjective
      visibleOf hnot

theorem regression_supportFullRule_property_decoder_constant_on_observed_fibers
    {α : Type*} (property : ExactVisibleRule Z k → α)
    (decode : (Block → Bool) → α)
    (hdecode :
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁) :
    property rule₀ = property rule₁ := by
  exact
    supportFullRule_propertyDecoder_constant_on_observedFibers
      visibleOf property decode hdecode hsame

theorem regression_supportFullRule_property_decoder_iff_constant_on_observed_fibers
    {α : Type*} (property : ExactVisibleRule Z k → α) :
    (∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule) ↔
      ∀ {rule₀ rule₁ : ExactVisibleRule Z k},
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ →
        property rule₀ = property rule₁ := by
  exact
    supportFullRule_exists_propertyDecoder_iff_constant_on_observedFibers
      visibleOf property

theorem regression_supportFullRule_no_property_decoder_of_same_output_ne
    {α : Type*} (property : ExactVisibleRule Z k → α)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁)
    (hprop : property rule₀ ≠ property rule₁) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule := by
  exact
    supportFullRule_not_exists_propertyDecoder_of_same_output_ne
      visibleOf property hsame hprop

theorem regression_supportFullRule_no_eval_decoder_of_missed_point
    (u₀ : ExactVisiblePostSwitchSurface Z k)
    (hmiss : ∀ phi, visibleOf phi ≠ u₀) :
    ¬ ∃ decode : (Block → Bool) → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule u₀ := by
  exact
    supportFullRule_not_exists_evalDecoder_of_missed_point
      visibleOf u₀ hmiss

theorem regression_supportFullRule_exists_eval_decoder_iff_mem_range
    (u₀ : ExactVisiblePostSwitchSurface Z k) :
    (∃ decode : (Block → Bool) → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule u₀) ↔ ∃ phi, visibleOf phi = u₀ := by
  exact
    supportFullRule_exists_evalDecoder_iff_mem_range
      visibleOf u₀

theorem regression_supportFullRule_all_eval_decoders_iff_surjective :
    (∀ u₀ : ExactVisiblePostSwitchSurface Z k,
      ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀) ↔ Function.Surjective visibleOf := by
  exact
    supportFullRule_all_evalDecoders_iff_visibleOf_surjective
      visibleOf

theorem regression_supportFullRule_exists_query_decoder_iff_forall_mem_range
    {Query : Type*} (queryOf : Query → ExactVisiblePostSwitchSurface Z k) :
    (∃ decode : (Block → Bool) → Query → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          fun q => rule (queryOf q)) ↔ ∀ q, ∃ phi, visibleOf phi = queryOf q := by
  exact
    supportFullRule_exists_queryDecoder_iff_forall_mem_range
      visibleOf queryOf

theorem regression_supportFullRule_no_query_decoder_of_missed_query
    {Query : Type*} (queryOf : Query → ExactVisiblePostSwitchSurface Z k)
    (q₀ : Query) (hmiss : ∀ phi, visibleOf phi ≠ queryOf q₀) :
    ¬ ∃ decode : (Block → Bool) → Query → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          fun q => rule (queryOf q) := by
  exact
    supportFullRule_not_exists_queryDecoder_of_missed_query
      visibleOf queryOf q₀ hmiss

theorem regression_supportFullRule_adaptive_query_decoder_of_all_queries_reachable
    {α : Type*}
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α)
    (hreach : AdaptiveBoolQueryTree.AllQueriesReachable visibleOf tree) :
    ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree := by
  exact
    supportFullRule_exists_adaptiveQueryDecoder_of_allQueriesReachable
      visibleOf tree hreach

theorem regression_supportFullRule_adaptive_query_decoder_iff_constant_on_observed_fibers
    {α : Type*}
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α) :
    (∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree) ↔
      ∀ {rule₀ rule₁ : ExactVisibleRule Z k},
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ →
        AdaptiveBoolQueryTree.eval rule₀ tree =
          AdaptiveBoolQueryTree.eval rule₁ tree := by
  exact
    supportFullRule_exists_adaptiveQueryDecoder_iff_constant_on_observedFibers
      visibleOf tree

theorem regression_supportFullRule_no_adaptive_query_decoder_of_same_output_eval_ne
    {α : Type*}
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁)
    (hne :
      AdaptiveBoolQueryTree.eval rule₀ tree ≠
        AdaptiveBoolQueryTree.eval rule₁ tree) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree := by
  exact
    supportFullRule_not_exists_adaptiveQueryDecoder_of_same_output_eval_ne
      visibleOf tree hsame hne

theorem regression_supportFullRule_no_root_adaptive_query_decoder_of_missed_point
    (u₀ : ExactVisiblePostSwitchSurface Z k)
    {α : Type*} {valueFalse valueTrue : α}
    (hmiss : ∀ phi, visibleOf phi ≠ u₀)
    (hne : valueFalse ≠ valueTrue) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule
            (AdaptiveBoolQueryTree.query u₀
              (AdaptiveBoolQueryTree.leaf valueFalse)
              (AdaptiveBoolQueryTree.leaf valueTrue)) := by
  exact
    supportFullRule_not_exists_rootAdaptiveQueryDecoder_of_missed_point_ne
      visibleOf u₀ hmiss hne

theorem regression_supportFullRule_exists_unobservable_eval_of_not_surjective
    (hnot : ¬ Function.Surjective visibleOf) :
    ∃ u₀ : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀ := by
  exact
    supportFullRule_exists_unobservable_eval_of_not_surjective
      visibleOf hnot

theorem regression_supportFullRule_no_observed_rule_injective_below_surface_card
    [Fintype Z] [Fintype Block]
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Injective
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict := by
  exact
    supportFullRule_not_observedRuleMap_injective_of_card_lt_surfaceCard
      visibleOf hcard

theorem regression_supportFullRule_card_small_off_support_rules_indistinguishable
    [Fintype Z] [Fintype Block]
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ rule₀ rule₁ : ExactVisibleRule Z k,
      rule₀ ≠ rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₀ ≠
          (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₁ := by
  exact
    supportFullRule_exists_distinct_rules_same_outputFamily_of_card_lt_surfaceCard
      visibleOf hcard

theorem regression_supportFullRule_no_exact_decoder_below_surface_card
    [Fintype Z] [Fintype Block]
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ decode : (Block → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule := by
  exact
    supportFullRule_not_exists_exactDecoder_of_card_lt_surfaceCard
      visibleOf hcard

theorem regression_supportFullRule_exists_unobservable_eval_below_surface_card
    [Fintype Z] [Fintype Block]
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ u₀ : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀ := by
  exact
    supportFullRule_exists_unobservable_eval_of_card_lt_surfaceCard
      visibleOf hcard

theorem regression_supportFullRule_uniform_section_transfers_cover_card
    [Fintype Block] {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
      (2 ^ Fintype.card Block) := by
  exact
    supportFullRule_predictorFamily_finitePredictorCover_card_of_uniformVisibleSection
      visibleOf hsec

theorem regression_supportFullRule_uniform_section_transfers_clocked_payload
    [Fintype Z] [Fintype Block] {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    ClockedKpolyFiniteLearningPayload
      (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily
      (Fintype.card Block) clock := by
  exact
    supportFullRule_clockedKpolyFiniteLearningPayload_card_of_uniformVisibleSection
      visibleOf hsec

theorem regression_supportFullRule_uniform_section_forces_surface_card_le_support_card
    [Fintype Z] [Fintype Block] {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ Fintype.card Block := by
  exact
    supportFullRule_surfaceCard_le_blockCard_of_uniformVisibleSection
      visibleOf hsec

theorem regression_supportFullRule_no_uniform_section_below_surface_card
    [Fintype Z] [Fintype Block]
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ sec : ExactVisiblePostSwitchSurface Z k → Block,
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec := by
  exact
    supportFullRule_not_hasUniformVisibleSection_of_card_lt_surfaceCard
      visibleOf hcard

theorem regression_supportFullRule_observed_small_not_full_cover
    [Fintype Z] [Fintype Block]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FinitePredictorCover
        (2 ^ Fintype.card Block) ∧
      ¬ (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  exact supportFullRule_observedSmall_and_not_exactVisibleCover visibleOf hs

theorem regression_supportFullRule_no_clocked_payload
    [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily s clock := by
  exact supportFullRule_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    visibleOf hs

end FiniteObservedSupport

end Mettapedia.Computability.PNP
