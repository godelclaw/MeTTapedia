import Mettapedia.Computability.PNP.CruxSynthesisRegressionKpolyBridgeExamplesData
import Mettapedia.Computability.PNP.CruxKpolyBitFallbackThresholdActualLocal

/-!
# Kpoly bridge example cardinality anchors

Regression anchors for uniform-cardinality and injective-extractor recovery thresholds.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
open scoped ENNReal

universe u v w z

local instance : Nonempty (ExactVisiblePostSwitchSurface (BitVec 1) 1) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

private theorem three_quarters_lt_seven_eighths_actualSparseRecoveryInjectiveBridge :
    (3 : ℝ≥0∞) / 4 < (7 : ℝ≥0∞) / 8 := by
  have h₁ : (3 : ℝ≥0∞) / 4 = 6 / 8 := by
    refine (ENNReal.div_eq_div_iff (by norm_num) (by simp) (by norm_num) (by simp)).2 ?_
    norm_num
  rw [h₁]
  exact ENNReal.div_lt_div_right (by norm_num) (by simp) (by norm_num)

theorem kpoly_anchor_surjective_actual_local_recovery_uniform_cardinality_threshold_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
          idBitVec1ActualSparseRecoveryCardinalityBridge
          q)) :
    1 - (Fintype.card (ExactVisiblePostSwitchSurface (BitVec 1) 1) : ℝ≥0∞)⁻¹ ≤ q := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_one_sub_inv_card_le_of_nonempty_recovery
      (k := 1)
      (r := 1)
      (T := fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 1)
      idBitVec1ActualSparseRecoveryCardinalityBridge
      h

theorem kpoly_anchor_full_rule_actual_local_recovery_bitvec_cardinality_threshold_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
          idBitVec1ActualSparseRecoveryCardinalityBridge
          q)) :
    1 - (2 ^ (1 + 2 * 1) : ℝ≥0∞)⁻¹ ≤ q := by
  exact
    kpolyCoverage_anchor_fullRuleActualLocal_one_sub_pow_inv_le_of_nonempty_recovery
      (k := 1)
      (r := 1)
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge)
      idBitVec1ActualSparseRecoveryCardinalityBridge
      h

theorem kpoly_anchor_full_rule_actual_local_no_extractor_recovery_bitvec_cardinality_threshold_regression :
    ¬ ∃ zfeat : BitVec 1 → BitVec 1,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
            (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
            zfeat
            0) := by
  exact
    kpolyCoverage_anchor_fullRuleActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (n := 1)
      (k := 1)
      (r := 1)
      bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
      (q := 0)
      (by
        rw [tsub_pos_iff_lt]
        exact ENNReal.inv_lt_one.2 (by norm_num))

theorem kpoly_anchor_actual_local_injective_recovery_uniform_cardinality_threshold_boundary_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge
          idBitVec1ActualSparseRecoveryCardinalityBridge
          q)) :
    1 - (Fintype.card (ExactVisiblePostSwitchSurface (BitVec 1) 1) : ℝ≥0∞)⁻¹ ≤ q := by
  exact
    kpolyCoverage_anchor_actualLocal_one_sub_inv_card_le_of_nonempty_recovery_of_injective_zfeat
      (k := 1)
      (r := 1)
      (T := constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge)
      (zfeat := idBitVec1ActualSparseRecoveryCardinalityBridge)
      ()
      (fun _ _ hxy => hxy)
      (by norm_num)
      h

theorem kpoly_anchor_actual_local_injective_recovery_bitvec_cardinality_threshold_boundary_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge
          idBitVec1ActualSparseRecoveryCardinalityBridge
          q)) :
    1 - (2 ^ (1 + 2 * 1) : ℝ≥0∞)⁻¹ ≤ q := by
  exact
    kpolyCoverage_anchor_actualLocal_one_sub_pow_inv_le_of_nonempty_recovery_of_injective_zfeat
      (k := 1)
      (r := 1)
      (T := constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge)
      (zfeat := idBitVec1ActualSparseRecoveryCardinalityBridge)
      ()
      (fun _ _ hxy => hxy)
      (by norm_num)
      h

theorem kpoly_anchor_actual_local_no_injective_extractor_recovery_bitvec_cardinality_threshold_regression :
    ¬ ∃ zfeat : BitVec 1 → BitVec 1,
        Function.Injective zfeat ∧
          Nonempty
            (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
              bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
              constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge
              zfeat
              ((3 : ℝ≥0∞) / 4)) := by
  exact
    kpolyCoverage_anchor_actualLocal_not_exists_injective_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (n := 1)
      (k := 1)
      (r := 1)
      bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
      constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge
      ((3 : ℝ≥0∞) / 4)
      ()
      (by norm_num)
      (by
        have hthreshold : 1 - (2 ^ 3 : ℝ≥0∞)⁻¹ = (7 : ℝ≥0∞) / 8 := by
          have hsum : (1 : ℝ≥0∞) = (7 : ℝ≥0∞) / 8 + (2 ^ 3 : ℝ≥0∞)⁻¹ := by
            have hinv : ((2 ^ 3 : ℝ≥0∞)⁻¹) = (1 : ℝ≥0∞) / 8 := by
              norm_num
            calc
              (1 : ℝ≥0∞) = (8 : ℝ≥0∞) / 8 := by
                    exact (ENNReal.div_self (by norm_num) (by simp)).symm
              _ = ((7 : ℝ≥0∞) + 1) / 8 := by norm_num
              _ = (7 : ℝ≥0∞) / 8 + (1 : ℝ≥0∞) / 8 := by
                    simpa using
                      (ENNReal.div_add_div_same
                        (a := (7 : ℝ≥0∞))
                        (b := (1 : ℝ≥0∞))
                        (c := (8 : ℝ≥0∞))).symm
              _ = (7 : ℝ≥0∞) / 8 + (2 ^ 3 : ℝ≥0∞)⁻¹ := by
                    rw [hinv]
          exact ENNReal.sub_eq_of_eq_add (by simp) hsum
        rw [hthreshold]
        exact three_quarters_lt_seven_eighths_actualSparseRecoveryInjectiveBridge)

end Mettapedia.Computability.PNP.CruxSynthesisRegression
