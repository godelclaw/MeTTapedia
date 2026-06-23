import Mettapedia.Computability.PNP.CruxKpolySubrepairCoverage
import Mettapedia.Computability.PNP.CruxKpolyCoverageClockedBridge
import Mettapedia.Computability.PNP.CruxKpolyCoverageSwitchedHistoryWrappers
import Mettapedia.Computability.PNP.CruxKpolyActualLocalExactZAB

/-!
# Regression checks for PNP Kpoly bridge status

This module contains Kpoly bridge-status membership wrappers and bridge-status
anchor regressions from the decomposed PNP crux synthesis harness.  It keeps
the historical `CruxSynthesisRegression` theorem namespace while isolating the
status layer from concrete examples and packet-status bookkeeping.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
open scoped ENNReal

universe u v w z

theorem current_pnp_kpoly_product_bound_bridge_finite_image_regression :
    PNPKpolySubrepairClass.productBoundBridgeFiniteImageBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.productBoundBridgeFiniteImageBoundary

theorem current_pnp_kpoly_fielded_switching_bridge_finite_image_regression :
    PNPKpolySubrepairClass.fieldedSwitchingBridgeFiniteImageBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fieldedSwitchingBridgeFiniteImageBoundary

theorem current_pnp_kpoly_product_bound_full_visible_regression :
    PNPKpolySubrepairClass.productBoundOnlyFullVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.productBoundOnlyFullVisibleObstruction

theorem current_pnp_kpoly_fielded_switching_full_visible_regression :
    PNPKpolySubrepairClass.fieldedSwitchingOnlyFullVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fieldedSwitchingOnlyFullVisibleObstruction

theorem current_pnp_kpoly_product_bound_surjective_visible_regression :
    PNPKpolySubrepairClass.productBoundOnlySurjectiveVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.productBoundOnlySurjectiveVisibleObstruction

theorem current_pnp_kpoly_fielded_switching_surjective_visible_regression :
    PNPKpolySubrepairClass.fieldedSwitchingOnlySurjectiveVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fieldedSwitchingOnlySurjectiveVisibleObstruction

theorem current_pnp_kpoly_product_bound_clocked_payload_boundary_regression :
    PNPKpolySubrepairClass.productBoundClockedPayloadBridgeFiniteImageBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.productBoundClockedPayloadBridgeFiniteImageBoundary

theorem current_pnp_kpoly_fielded_switching_clocked_payload_boundary_regression :
    PNPKpolySubrepairClass.fieldedSwitchingClockedPayloadBridgeFiniteImageBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fieldedSwitchingClockedPayloadBridgeFiniteImageBoundary

theorem current_pnp_kpoly_product_bound_clocked_payload_full_visible_regression :
    PNPKpolySubrepairClass.productBoundOnlyClockedPayloadFullVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.productBoundOnlyClockedPayloadFullVisibleObstruction

theorem current_pnp_kpoly_fielded_switching_clocked_payload_full_visible_regression :
    PNPKpolySubrepairClass.fieldedSwitchingOnlyClockedPayloadFullVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fieldedSwitchingOnlyClockedPayloadFullVisibleObstruction

theorem current_pnp_kpoly_product_bound_clocked_payload_surjective_regression :
    PNPKpolySubrepairClass.productBoundOnlyClockedPayloadSurjectiveVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.productBoundOnlyClockedPayloadSurjectiveVisibleObstruction

theorem current_pnp_kpoly_fielded_switching_clocked_payload_surjective_regression :
    PNPKpolySubrepairClass.fieldedSwitchingOnlyClockedPayloadSurjectiveVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fieldedSwitchingOnlyClockedPayloadSurjectiveVisibleObstruction

theorem current_pnp_kpoly_actual_switched_history_bitvec_full_width_interval_regression :
    PNPKpolySubrepairClass.actualSwitchedHistoryBitVecFullWidthIntervalObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualSwitchedHistoryBitVecFullWidthIntervalObstruction

theorem current_pnp_kpoly_actual_switched_history_bitvec_full_width_interval_clocked_payload_regression :
    PNPKpolySubrepairClass.actualSwitchedHistoryBitVecFullWidthIntervalClockedPayloadObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualSwitchedHistoryBitVecFullWidthIntervalClockedPayloadObstruction

theorem kpoly_anchor_full_rule_actual_switched_history_exact_visible_interval_regression :
    ¬ ActualSwitchedLocalInterface.SwitchedHistoryExactVisibleCompressionWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
        4
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) := by
  exact
    kpolyCoverage_anchor_not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_fullWidthBudget
      (T := fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
      (s := 4)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 1)
      (by norm_num)
      (by norm_num)

theorem kpoly_anchor_full_rule_actual_switched_history_clocked_interval_regression :
    ¬ ActualSwitchedLocalInterface.SwitchedHistoryClockedKpolyFiniteLearningWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
        4
        0
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) := by
  exact
    kpolyCoverage_anchor_not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_fullWidthBudget
      (T := fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
      (s := 4) (clock := 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 1)
      (by norm_num)
      (by norm_num)

theorem current_pnp_kpoly_support_full_rule_output_family_factor_regression :
    PNPKpolySubrepairClass.supportFullRuleOutputFamilyFactorBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleOutputFamilyFactorBoundary

theorem current_pnp_kpoly_support_full_rule_observed_rule_injective_surjective_regression :
    PNPKpolySubrepairClass.supportFullRuleObservedRuleInjectiveSurjectiveBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleObservedRuleInjectiveSurjectiveBoundary

theorem current_pnp_kpoly_support_full_rule_exact_decoder_surjective_regression :
    PNPKpolySubrepairClass.supportFullRuleExactDecoderSurjectiveBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleExactDecoderSurjectiveBoundary

theorem current_pnp_kpoly_support_full_rule_observed_rule_map_noninjective_regression :
    PNPKpolySubrepairClass.supportFullRuleObservedRuleMapNoninjectiveBelowSurfaceCard ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleObservedRuleMapNoninjectiveBelowSurfaceCard

theorem current_pnp_kpoly_support_full_rule_distinct_rules_same_output_regression :
    PNPKpolySubrepairClass.supportFullRuleDistinctRulesSameOutputBelowSurfaceCard ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleDistinctRulesSameOutputBelowSurfaceCard

theorem current_pnp_kpoly_support_full_rule_property_decoder_constancy_regression :
    PNPKpolySubrepairClass.supportFullRulePropertyDecoderFiberConstancyBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRulePropertyDecoderFiberConstancyBoundary

theorem current_pnp_kpoly_support_full_rule_property_decoder_iff_regression :
    PNPKpolySubrepairClass.supportFullRulePropertyDecoderIffFiberConstancyBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRulePropertyDecoderIffFiberConstancyBoundary

theorem current_pnp_kpoly_support_full_rule_no_property_decoder_regression :
    PNPKpolySubrepairClass.supportFullRuleNoPropertyDecoderSameOutputBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleNoPropertyDecoderSameOutputBoundary

theorem current_pnp_kpoly_support_full_rule_eval_decoder_range_regression :
    PNPKpolySubrepairClass.supportFullRuleEvalDecoderRangeBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleEvalDecoderRangeBoundary

theorem current_pnp_kpoly_support_full_rule_all_eval_decoders_surjective_regression :
    PNPKpolySubrepairClass.supportFullRuleAllEvalDecodersSurjectiveBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleAllEvalDecodersSurjectiveBoundary

theorem current_pnp_kpoly_support_full_rule_query_decoder_range_regression :
    PNPKpolySubrepairClass.supportFullRuleQueryDecoderRangeBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleQueryDecoderRangeBoundary

theorem current_pnp_kpoly_support_full_rule_no_query_decoder_missed_query_regression :
    PNPKpolySubrepairClass.supportFullRuleNoQueryDecoderMissedQueryBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleNoQueryDecoderMissedQueryBoundary

theorem current_pnp_kpoly_support_full_rule_adaptive_query_decoder_reachable_regression :
    PNPKpolySubrepairClass.supportFullRuleAdaptiveQueryDecoderReachableBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleAdaptiveQueryDecoderReachableBoundary

theorem current_pnp_kpoly_support_full_rule_adaptive_query_decoder_iff_regression :
    PNPKpolySubrepairClass.supportFullRuleAdaptiveQueryDecoderIffFiberConstancyBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleAdaptiveQueryDecoderIffFiberConstancyBoundary

theorem current_pnp_kpoly_support_full_rule_no_adaptive_query_decoder_regression :
    PNPKpolySubrepairClass.supportFullRuleNoAdaptiveQueryDecoderSameOutputEvalBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleNoAdaptiveQueryDecoderSameOutputEvalBoundary

theorem current_pnp_kpoly_support_full_rule_no_root_adaptive_query_decoder_regression :
    PNPKpolySubrepairClass.supportFullRuleNoRootAdaptiveQueryDecoderMissedPointBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleNoRootAdaptiveQueryDecoderMissedPointBoundary

theorem current_pnp_kpoly_support_full_rule_no_exact_decoder_regression :
    PNPKpolySubrepairClass.supportFullRuleNoExactDecoderBelowSurfaceCard ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleNoExactDecoderBelowSurfaceCard

theorem current_pnp_kpoly_support_full_rule_unobservable_eval_regression :
    PNPKpolySubrepairClass.supportFullRuleUnobservableEvalBelowSurfaceCard ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleUnobservableEvalBelowSurfaceCard

theorem current_pnp_kpoly_support_full_rule_observed_small_cover_regression :
    PNPKpolySubrepairClass.supportFullRuleObservedSmallNotExactVisibleCoverBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleObservedSmallNotExactVisibleCoverBoundary

theorem current_pnp_kpoly_support_full_rule_not_clocked_payload_regression :
    PNPKpolySubrepairClass.supportFullRuleNotClockedPayloadBelowSurfaceCard ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleNotClockedPayloadBelowSurfaceCard

theorem current_pnp_kpoly_support_full_rule_uniform_section_finite_cover_regression :
    PNPKpolySubrepairClass.supportFullRuleUniformSectionFinitePredictorCoverBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleUniformSectionFinitePredictorCoverBoundary

theorem current_pnp_kpoly_support_full_rule_uniform_section_clocked_payload_regression :
    PNPKpolySubrepairClass.supportFullRuleUniformSectionClockedPayloadBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleUniformSectionClockedPayloadBoundary

theorem current_pnp_kpoly_support_full_rule_uniform_section_surface_card_regression :
    PNPKpolySubrepairClass.supportFullRuleUniformSectionSurfaceCardBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleUniformSectionSurfaceCardBoundary

theorem current_pnp_kpoly_support_full_rule_no_uniform_section_regression :
    PNPKpolySubrepairClass.supportFullRuleNoUniformSectionBelowSurfaceCard ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleNoUniformSectionBelowSurfaceCard

theorem current_pnp_kpoly_one_block_full_rule_observed_small_cover_regression :
    PNPKpolySubrepairClass.oneBlockFullRuleObservedSmallNotExactVisibleCoverBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.oneBlockFullRuleObservedSmallNotExactVisibleCoverBoundary

theorem current_pnp_kpoly_one_block_full_rule_not_clocked_payload_regression :
    PNPKpolySubrepairClass.oneBlockFullRuleNotClockedPayloadBelowSurfaceCard ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.oneBlockFullRuleNotClockedPayloadBelowSurfaceCard

theorem current_pnp_kpoly_one_block_full_rule_no_exact_decoder_regression :
    PNPKpolySubrepairClass.oneBlockFullRuleNoExactDecoderOneLtSurfaceCardBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.oneBlockFullRuleNoExactDecoderOneLtSurfaceCardBoundary

theorem current_pnp_kpoly_one_block_full_rule_unobservable_eval_regression :
    PNPKpolySubrepairClass.oneBlockFullRuleUnobservableEvalOneLtSurfaceCardBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.oneBlockFullRuleUnobservableEvalOneLtSurfaceCardBoundary

theorem kpoly_anchor_product_bound_clocked_payload_bridge_iff_finite_image_regression
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    kpolyCoverage_anchor_productBoundOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge

theorem kpoly_anchor_fielded_switching_clocked_payload_bridge_iff_finite_image_regression
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    kpolyCoverage_anchor_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge

theorem kpoly_anchor_exact_zab_recovery_large_region_disagreement_regression
    {Z : Type u} [Fintype Z] {r k : ℕ} {Index : Type v}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hmass : q < region.sum (fun x => μ x)) :
    ∃ x, x ∈ region ∧ μ x ≠ 0 ∧
      (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x ≠
        G.predict i x := by
  exact
    kpolyCoverage_anchor_exactZABERMRecoveryData_exists_pos_mass_disagreement_in_region_of_badCode
      h i c region hmass

end Mettapedia.Computability.PNP.CruxSynthesisRegression
