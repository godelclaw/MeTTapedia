import Mettapedia.Computability.PNP.CruxSynthesisRegressionKpolyBridgeExamplesData
import Mettapedia.Computability.PNP.CruxKpolyBitFallbackThresholdRegions
import Mettapedia.Computability.PNP.CruxKpolyBitFallbackThresholdVisibleWidth

/-!
# Kpoly bridge example threshold anchors

Regression anchors for threshold-width, pairwise-agreement, and visible-budget obstructions.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
open scoped ENNReal

universe u v w z

private theorem half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression {p : ℕ}
    (hp : (2 : ℝ≥0∞) < 2 ^ p) :
    ((1 : ℝ≥0∞) / 2) < 1 - (2 ^ p : ℝ≥0∞)⁻¹ := by
  have hhalf : ((1 : ℝ≥0∞) / 2) = 1 - (2 : ℝ≥0∞)⁻¹ := by
    calc
      ((1 : ℝ≥0∞) / 2) = (2 : ℝ≥0∞)⁻¹ := by simp
      _ = 1 - (2 : ℝ≥0∞)⁻¹ := ENNReal.one_sub_inv_two.symm
  rw [hhalf]
  refine (ENNReal.sub_lt_iff_lt_left ?_ ?_).2 ?_
  · simp
  · simp
  have hinv_lt : (2 ^ p : ℝ≥0∞)⁻¹ < (2 : ℝ≥0∞)⁻¹ := by
    simpa using ENNReal.inv_lt_inv' hp
  have hpow_ge_one : (1 : ℝ≥0∞) ≤ 2 ^ p := by
    exact le_of_lt <| lt_trans (by norm_num : (1 : ℝ≥0∞) < 2) hp
  have hinv_le_one : (2 ^ p : ℝ≥0∞)⁻¹ ≤ 1 := by
    simpa using ENNReal.inv_le_inv' hpow_ge_one
  calc
    1 = (1 - (2 ^ p : ℝ≥0∞)⁻¹) + (2 ^ p : ℝ≥0∞)⁻¹ := by
      symm
      exact tsub_add_cancel_of_le hinv_le_one
    _ < (1 - (2 ^ p : ℝ≥0∞)⁻¹) + (2 : ℝ≥0∞)⁻¹ := by
      exact ENNReal.add_lt_add_left (by simp) hinv_lt
    _ = (2 : ℝ≥0∞)⁻¹ + (1 - (2 ^ p : ℝ≥0∞)⁻¹) := by
      rw [add_comm]

theorem kpoly_anchor_full_rule_actual_local_recovery_threshold_width_boundary_regression
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
          idBitVec1ActualSparseRecoveryCardinalityBridge
          ((1 : ℝ≥0∞) / 2))) :
    1 + 2 * 1 < 4 := by
  exact
    kpolyCoverage_anchor_fullRuleActualLocal_visibleWidth_lt_of_nonempty_recovery_of_lt_one_sub_pow_inv
      (k := 1)
      (r := 1)
      (p := 4)
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge)
      idBitVec1ActualSparseRecoveryCardinalityBridge
      h
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 4))

theorem kpoly_anchor_full_rule_actual_local_no_extractor_recovery_threshold_width_regression :
    ¬ ∃ zfeat : BitVec 1 → BitVec 1,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
            (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
            zfeat
            ((1 : ℝ≥0∞) / 2)) := by
  exact
    kpolyCoverage_anchor_fullRuleActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_le_visibleWidth
      (n := 1)
      (k := 1)
      (r := 1)
      (p := 3)
      bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
      (((1 : ℝ≥0∞) / 2))
      (by norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 3))

theorem kpoly_anchor_bounded_sample_plugin_majority_actual_local_recovery_threshold_width_boundary_regression
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 1) 1 8)
          idBitVec1ActualSparseRecoveryCardinalityBridge
          ((1 : ℝ≥0∞) / 2))) :
    1 + 2 * 1 < 4 := by
  exact
    kpolyCoverage_anchor_boundedSamplePluginMajorityActualLocal_visibleWidth_lt_of_nonempty_recovery_of_lt_one_sub_pow_inv
      (k := 1)
      (r := 1)
      (sampleBound := 8)
      (p := 4)
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge)
      idBitVec1ActualSparseRecoveryCardinalityBridge
      h
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 4))

theorem kpoly_anchor_bounded_sample_plugin_majority_actual_local_no_extractor_recovery_threshold_width_regression :
    ¬ ∃ zfeat : BitVec 1 → BitVec 1,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
            (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 1) 1 8)
            zfeat
            ((1 : ℝ≥0∞) / 2)) := by
  exact
    kpolyCoverage_anchor_boundedSamplePluginMajorityActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_le_visibleWidth
      (n := 1)
      (k := 1)
      (r := 1)
      (sampleBound := 8)
      (p := 3)
      bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
      (((1 : ℝ≥0∞) / 2))
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (by norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 3))

theorem kpoly_anchor_actual_local_recovery_pairwise_agreement_boundary_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3PureMeasureActualSparseRecoveryPayloadBridge
          fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge
          fin3ToBitVec0ActualSparseRecoveryPayloadBridge
          q)) :
    agreementMass
        fin3PureMeasureActualSparseRecoveryPayloadBridge
        (fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge.predictorFamily.predict 0)
        (fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge.predictorFamily.predict 2)
      ≤ q := by
  exact
    kpolyCoverage_anchor_actualLocal_agreementMass_le_of_nonempty_recovery_of_predict_ne
      (k := 0)
      (r := 0)
      (T := fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge)
      (μ := fin3PureMeasureActualSparseRecoveryPayloadBridge)
      (q := q)
      fin3ToBitVec0ActualSparseRecoveryPayloadBridge
      h
      0
      2
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge_predict_zero_ne_predict_two.symm

private noncomputable def fin5ProbeActualSparseRecoveryPayloadThreeQuartersBridge : ℝ≥0∞ :=
  (3 : ℝ≥0∞) / 4

private theorem fin5ProbeActualSparseRecoveryPayloadThreeQuartersBridge_lt_one :
    fin5ProbeActualSparseRecoveryPayloadThreeQuartersBridge < 1 := by
  have h₁ : fin5ProbeActualSparseRecoveryPayloadThreeQuartersBridge = (3 : ℝ≥0∞) / 4 := by
    rfl
  have h₂ : (1 : ℝ≥0∞) = (4 : ℝ≥0∞) / 4 := by
    rw [ENNReal.div_self (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)]
  rw [h₁, h₂]
  exact ENNReal.div_lt_div_right (by norm_num) (by simp) (by norm_num)

theorem kpoly_anchor_actual_local_no_extractor_recovery_pairwise_agreement_regression :
    ¬ ∃ zfeat : Fin 3 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            fin3PureMeasureActualSparseRecoveryPayloadBridge
            fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge
            zfeat
            fin5ProbeActualSparseRecoveryPayloadThreeQuartersBridge) := by
  exact
    kpolyCoverage_anchor_actualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_agreementMass_of_predict_ne
      (Z := Fin 3)
      (k := 0)
      (r := 0)
      (μ := fin3PureMeasureActualSparseRecoveryPayloadBridge)
      (T := fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge)
      (q := fin5ProbeActualSparseRecoveryPayloadThreeQuartersBridge)
      0
      2
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge_predict_zero_ne_predict_two.symm
      (by
        rw [fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge_agreementMass_predict_zero_predict_two_eq_one]
        exact fin5ProbeActualSparseRecoveryPayloadThreeQuartersBridge_lt_one)

theorem kpoly_anchor_full_rule_actual_local_recovery_threshold_visible_budget_boundary_regression
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
          zeroBitVec1ToBitVec0ActualSparseRecoveryThresholdVisibleBudgetBridge
          ((1 : ℝ≥0∞) / 2))) :
    1 ≤ 2 * 0 + 2 * 1 + 0 := by
  exact
    kpolyCoverage_anchor_fullRuleActualLocal_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_add_slack_of_nonempty_recovery_of_lt_one_sub_pow_inv
      (k := 1)
      (r := 0)
      (slack := 0)
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge)
      zeroBitVec1ToBitVec0ActualSparseRecoveryThresholdVisibleBudgetBridge
      h
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 5))

theorem kpoly_anchor_full_rule_actual_local_no_extractor_recovery_threshold_visible_budget_regression :
    ¬ ∃ zfeat : BitVec 3 → BitVec 1,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec3k0UniformMeasureActualSparseRecoveryThresholdVisibleBudgetBridge
            (fullRuleActualSwitchedLocalInterface (BitVec 3) 0)
            zfeat
            ((1 : ℝ≥0∞) / 2)) := by
  exact
    kpolyCoverage_anchor_fullRuleActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_two_mul_extractorWidth_add_two_mul_k_add_slack_lt_visibleWidth
      (n := 3)
      (k := 0)
      (r := 1)
      (slack := 0)
      bitVec3k0UniformMeasureActualSparseRecoveryThresholdVisibleBudgetBridge
      (((1 : ℝ≥0∞) / 2))
      (by norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 3))

theorem kpoly_anchor_bounded_sample_plugin_majority_actual_local_recovery_threshold_visible_budget_boundary_regression
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 1) 1 8)
          zeroBitVec1ToBitVec0ActualSparseRecoveryThresholdVisibleBudgetBridge
          ((1 : ℝ≥0∞) / 2))) :
    1 ≤ 2 * 0 + 2 * 1 + 0 := by
  exact
    kpolyCoverage_anchor_boundedSamplePluginMajorityActualLocal_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_add_slack_of_nonempty_recovery_of_lt_one_sub_pow_inv
      (k := 1)
      (r := 0)
      (sampleBound := 8)
      (slack := 0)
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge)
      zeroBitVec1ToBitVec0ActualSparseRecoveryThresholdVisibleBudgetBridge
      h
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 5))

theorem kpoly_anchor_bounded_sample_plugin_majority_actual_local_no_extractor_recovery_threshold_visible_budget_regression :
    ¬ ∃ zfeat : BitVec 3 → BitVec 1,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec3k0UniformMeasureActualSparseRecoveryThresholdVisibleBudgetBridge
            (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 3) 0 8)
            zfeat
            ((1 : ℝ≥0∞) / 2)) := by
  exact
    kpolyCoverage_anchor_boundedSamplePluginMajorityActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_two_mul_extractorWidth_add_two_mul_k_add_slack_lt_visibleWidth
      (n := 3)
      (k := 0)
      (r := 1)
      (sampleBound := 8)
      (slack := 0)
      bitVec3k0UniformMeasureActualSparseRecoveryThresholdVisibleBudgetBridge
      (((1 : ℝ≥0∞) / 2))
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (by norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 3))

end Mettapedia.Computability.PNP.CruxSynthesisRegression
