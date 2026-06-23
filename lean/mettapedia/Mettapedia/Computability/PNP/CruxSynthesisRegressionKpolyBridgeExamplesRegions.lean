import Mettapedia.Computability.PNP.CruxSynthesisRegressionKpolyBridgeExamplesData
import Mettapedia.Computability.PNP.CruxKpolyBitFallbackThresholdRegions

/-!
# Kpoly bridge example region anchors

Regression anchors for proper-region mass and heavy-region trace-card obstructions.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
open scoped ENNReal

universe u v w z

noncomputable local instance : DecidableEq (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  Classical.decEq _

private noncomputable def fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge :
    ℝ≥0∞ :=
  (3 : ℝ≥0∞) / 4

private theorem fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge_lt_one :
    fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge < 1 := by
  have h₁ :
      fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge = (3 : ℝ≥0∞) / 4 := by
    rfl
  have h₂ : (1 : ℝ≥0∞) = (4 : ℝ≥0∞) / 4 := by
    rw [ENNReal.div_self (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)]
  rw [h₁, h₂]
  exact ENNReal.div_lt_div_right (by norm_num) (by simp) (by norm_num)

private theorem fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge_lt_regionMass :
    fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge <
      fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge.sum
        (fun x => fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge x) := by
  rw [fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge_mass_eq_one]
  exact fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge_lt_one


theorem kpoly_anchor_surjective_actual_local_recovery_proper_region_mass_boundary_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k0PureMeasureActualSparseRecoveryRegionBridge
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          zeroBitVec1ToBitVec0ActualSparseRecoveryThresholdVisibleBudgetBridge
          q)) :
    1 ≤ q := by
  have hbound :=
    kpolyCoverage_anchor_surjectiveActualLocal_regionMass_le_of_nonempty_recovery_of_exists_not_mem
      (k := 0)
      (r := 0)
      (T := fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
      (μ := bitVec1k0PureMeasureActualSparseRecoveryRegionBridge)
      (q := q)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 0)
      zeroBitVec1ToBitVec0ActualSparseRecoveryThresholdVisibleBudgetBridge
      h
      bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge
      (by
        exact ⟨bitVec1k0OneVisiblePointActualSparseRecoveryRegionBridge, by
          simp [bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge,
            bitVec1k0OneVisiblePointActualSparseRecoveryRegionBridge,
            bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge]⟩)
  have hmass_eq :
      bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge.sum
          (fun x => bitVec1k0PureMeasureActualSparseRecoveryRegionBridge x) = 1 := by
    simp [bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge,
      bitVec1k0PureMeasureActualSparseRecoveryRegionBridge,
      bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge]
  rw [hmass_eq] at hbound
  exact hbound

theorem kpoly_anchor_surjective_actual_local_no_extractor_recovery_proper_region_mass_regression :
    ¬ ∃ zfeat : BitVec 1 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec1k0PureMeasureActualSparseRecoveryRegionBridge
            (fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
            zfeat
            0) := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_exists_not_mem_of_lt_regionMass
      (Z := BitVec 1)
      (k := 0)
      (r := 0)
      bitVec1k0PureMeasureActualSparseRecoveryRegionBridge
      (fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
      (q := 0)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 0)
      bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge
      (by
        exact ⟨bitVec1k0OneVisiblePointActualSparseRecoveryRegionBridge, by
          simp [bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge,
            bitVec1k0OneVisiblePointActualSparseRecoveryRegionBridge,
            bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge]⟩)
      (by
        have hmass_eq :
            bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge.sum
                (fun x => bitVec1k0PureMeasureActualSparseRecoveryRegionBridge x) = 1 := by
          simp [bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge,
            bitVec1k0PureMeasureActualSparseRecoveryRegionBridge,
            bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge]
        rw [hmass_eq]
        norm_num)

theorem kpoly_anchor_actual_local_recovery_heavy_region_trace_card_boundary_regression
    {q : ℝ≥0∞}
    (hmass :
      q <
        fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge.sum
          (fun x => fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge x))
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge
          fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge
          fin3ToBitVec0ActualSparseRecoveryPayloadBridge
          q)) :
    Fintype.card (Fin 5) ≤
      2 ^ fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge.card := by
  exact
    kpolyCoverage_anchor_actualLocal_predictorCard_le_two_pow_regionCard_of_nonempty_recovery_of_injective_predict_of_lt_regionMass
      (μ := fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge)
      (T := fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge)
      (Index := Fin 5)
      (r := 0)
      (zfeat := fin3ToBitVec0ActualSparseRecoveryPayloadBridge)
      h
      fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge
      hmass
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge_injective_predict

theorem kpoly_anchor_actual_local_no_extractor_recovery_heavy_region_trace_card_regression :
    ¬ ∃ zfeat : Fin 3 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge
            fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge
            zfeat
            fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge) := by
  have hcard :
      2 ^ fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge.card <
        Fintype.card (Fin 5) := by
    rw [fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge_card]
    norm_num
  exact
    kpolyCoverage_anchor_actualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_regionCard_of_injective_predict_of_lt_regionMass
      (Z := Fin 3)
      (k := 0)
      (r := 0)
      (Index := Fin 5)
      (μ := fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge)
      (T := fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge)
      (q := fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge)
      fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge_injective_predict
      fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge_lt_regionMass
      hcard

end Mettapedia.Computability.PNP.CruxSynthesisRegression
