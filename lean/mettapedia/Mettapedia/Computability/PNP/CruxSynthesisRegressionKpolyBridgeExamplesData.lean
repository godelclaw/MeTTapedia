import Mettapedia.Computability.PNP.ActualSwitchedLocalFamily
import Mettapedia.Computability.PNP.ExactVisibleCompressionObstruction
import Mettapedia.Computability.PNP.FiniteIIDAgreement
import Mettapedia.Computability.PNP.SharedExactZABSparseThresholdSharpnessRawBitVec
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-!
# Regression checks for concrete PNP Kpoly bridge examples

This module contains the finite `Fin`/`BitVec` bridge examples and actual
sparse-recovery regression anchors from the decomposed PNP crux synthesis
harness.  It keeps the historical `CruxSynthesisRegression` theorem namespace
while isolating the concrete example layer from packet-status bookkeeping.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
open scoped ENNReal

universe u v w z

def oneBitVec1ActualSparseRecoveryBridge : BitVec 1 := fun _ => true

@[simp] theorem oneBitVec1ActualSparseRecoveryBridge_ne_zeroVec :
    oneBitVec1ActualSparseRecoveryBridge ≠ (zeroVec : BitVec 1) := by
  intro h
  have h0 := congrFun h 0
  simp [oneBitVec1ActualSparseRecoveryBridge, zeroVec] at h0

def fin3ToBitVec0ActualSparseRecoveryPayloadBridge : Fin 3 → BitVec 0 := fun _ => zeroVec

noncomputable def fin3ZeroVisiblePointActualSparseRecoveryPayloadBridge :
    ExactVisiblePostSwitchSurface (Fin 3) 0 :=
  ⟨0, zeroVec, zeroVec⟩

noncomputable def fin3OneVisiblePointActualSparseRecoveryPayloadBridge :
    ExactVisiblePostSwitchSurface (Fin 3) 0 :=
  ⟨1, zeroVec, zeroVec⟩

noncomputable def fin3TwoVisiblePointActualSparseRecoveryPayloadBridge :
    ExactVisiblePostSwitchSurface (Fin 3) 0 :=
  ⟨2, zeroVec, zeroVec⟩

noncomputable def fin3PureMeasureActualSparseRecoveryPayloadBridge :
    PMF (ExactVisiblePostSwitchSurface (Fin 3) 0) :=
  PMF.pure fin3ZeroVisiblePointActualSparseRecoveryPayloadBridge

theorem fullRuleActualSwitchedLocalInterface_lt_predictorCard_fin3k0r0_payload_bridge_regression :
    2 ^ (2 * allAffinePointBlockFeatureCount (0 + (0 + 0))) <
      2 ^ Fintype.card (ExactVisiblePostSwitchSurface (Fin 3) 0) := by
  rw [card_exactVisiblePostSwitchSurface (Z := Fin 3) (k := 0)]
  norm_num [allAffinePointBlockFeatureCount_eq]

def fin5ProbeFamilyActualSparseRecoveryPayloadBridge
    (p : Fin 5) :
    ExactVisiblePostSwitchSurface (Fin 3) 0 → Bool :=
  match p.1 with
  | 0 => fun _ => false
  | 1 => fun u => decide (u.z = 0)
  | 2 => fun u => decide (u.z = 1)
  | 3 => fun u => decide (u.z = 2)
  | _ => fun _ => true

theorem fin5ProbeFamilyActualSparseRecoveryPayloadBridge_injective :
    Function.Injective fin5ProbeFamilyActualSparseRecoveryPayloadBridge := by
  decide

theorem fin5ProbeFamilyActualSparseRecoveryPayloadBridge_lt_card_regression :
    2 ^ (2 * allAffinePointBlockFeatureCount (0 + (0 + 0))) < Fintype.card (Fin 5) := by
  norm_num [allAffinePointBlockFeatureCount_eq]

def fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge :
    ActualSwitchedLocalInterface
      (Fin 3)
      0
      (Fin 5)
      (ExactVisiblePostSwitchSurface (Fin 3) 0) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fin5ProbeFamilyActualSparseRecoveryPayloadBridge
  output := fun p u => fin5ProbeFamilyActualSparseRecoveryPayloadBridge p u
  output_eq_local := by
    intro p u
    rfl

theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge_injective_predict :
    Function.Injective
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge.predictorFamily.predict := by
  exact fin5ProbeFamilyActualSparseRecoveryPayloadBridge_injective

theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge_predict_zero_ne_predict_two :
    fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge.predictorFamily.predict 0 ≠
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge.predictorFamily.predict 2 := by
  intro h
  have hinj :=
    fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge_injective_predict
  have h02 : (0 : Fin 5) ≠ 2 := by decide
  exact h02 (hinj h)

theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge_agreementMass_predict_zero_predict_two_eq_one :
    agreementMass
        fin3PureMeasureActualSparseRecoveryPayloadBridge
        (fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge.predictorFamily.predict 0)
        (fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge.predictorFamily.predict 2)
      = 1 := by
  apply agreementMass_pure_eq_one_of_agrees
  simp [fin3ZeroVisiblePointActualSparseRecoveryPayloadBridge,
    fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge,
    fin5ProbeFamilyActualSparseRecoveryPayloadBridge]

def exactVisiblePostSwitchSurfaceFin30EquivActualSparseRecoveryHeavyRegionTraceBridge :
    ExactVisiblePostSwitchSurface (Fin 3) 0 ≃ Fin 3 where
  toFun u := u.z
  invFun z := ⟨z, zeroVec, zeroVec⟩
  left_inv := by
    intro u
    cases u with
    | mk z a b =>
        have ha : (zeroVec : BitVec 0) = a := Subsingleton.elim _ _
        have hb : (zeroVec : BitVec 0) = b := Subsingleton.elim _ _
        cases ha
        cases hb
        rfl
  right_inv := by
    intro z
    rfl

noncomputable def fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge :
    PMF (ExactVisiblePostSwitchSurface (Fin 3) 0) :=
  PMF.ofFintype
    (fun u => if u.z = 2 then 0 else (2 : ℝ≥0∞)⁻¹)
    (by
      classical
      have hsum :
          ∑ a : ExactVisiblePostSwitchSurface (Fin 3) 0,
              (if a.z = 2 then 0 else (2 : ℝ≥0∞)⁻¹)
            =
          ∑ b : Fin 3, (if b = 2 then 0 else (2 : ℝ≥0∞)⁻¹) := by
        simpa using
          (Fintype.sum_equiv
            exactVisiblePostSwitchSurfaceFin30EquivActualSparseRecoveryHeavyRegionTraceBridge
            (fun u : ExactVisiblePostSwitchSurface (Fin 3) 0 =>
              if u.z = 2 then 0 else (2 : ℝ≥0∞)⁻¹)
            (fun b : Fin 3 => if b = 2 then 0 else (2 : ℝ≥0∞)⁻¹)
            (by
              intro b
              rfl))
      calc
        ∑ a : ExactVisiblePostSwitchSurface (Fin 3) 0,
            (if a.z = 2 then 0 else (2 : ℝ≥0∞)⁻¹)
          =
            ∑ b : Fin 3, (if b = 2 then 0 else (2 : ℝ≥0∞)⁻¹) := hsum
        _ = 1 := by
          rw [Fin.sum_univ_three]
          simpa [two_mul] using ENNReal.inv_two_add_inv_two)

noncomputable def fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge :
    Finset (ExactVisiblePostSwitchSurface (Fin 3) 0) :=
  by
    classical
    exact
      insert
        fin3ZeroVisiblePointActualSparseRecoveryPayloadBridge
        {fin3OneVisiblePointActualSparseRecoveryPayloadBridge}

theorem fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge_card :
    fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge.card = 2 := by
  simp [fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge,
    fin3ZeroVisiblePointActualSparseRecoveryPayloadBridge,
    fin3OneVisiblePointActualSparseRecoveryPayloadBridge]

theorem fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge_mass_eq_one :
    fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge.sum
        (fun x => fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge x) = 1 := by
  calc
    fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge.sum
        (fun x => fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge x)
      = (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ := by
          simp [fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge,
            fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge,
            fin3ZeroVisiblePointActualSparseRecoveryPayloadBridge,
            fin3OneVisiblePointActualSparseRecoveryPayloadBridge]
    _ = 1 := by
      simpa [two_mul] using ENNReal.inv_two_add_inv_two


def idBitVec1ActualSparseRecoveryCardinalityBridge : BitVec 1 → BitVec 1 := fun x => x

local instance exactVisiblePostSwitchSurfaceBitVec1k1NonemptyBridge :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 1) 1) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

noncomputable def bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge :
    PMF (ExactVisiblePostSwitchSurface (BitVec 1) 1) :=
  PMF.uniformOfFintype _

def constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge :
    ActualSwitchedLocalInterface
      (BitVec 1)
      1
      Unit
      (ExactVisiblePostSwitchSurface (BitVec 1) 1) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun _ _ => false
  output := fun _ _ => false
  output_eq_local := by
    intro _ _
    rfl

theorem constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge_not_surjective :
    ¬ Function.Surjective
        constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge.predictorFamily.predict := by
  intro hsurj
  rcases hsurj (fun _ => true) with ⟨u, htrue⟩
  cases u
  have h := congrFun htrue ⟨zeroVec, zeroVec, zeroVec⟩
  simp [constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge] at h

noncomputable def bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge :
    ExactVisiblePostSwitchSurface (BitVec 1) 0 :=
  ⟨zeroVec, zeroVec, zeroVec⟩

noncomputable def bitVec1k0OneVisiblePointActualSparseRecoveryRegionBridge :
    ExactVisiblePostSwitchSurface (BitVec 1) 0 :=
  ⟨oneBitVec1ActualSparseRecoveryBridge, zeroVec, zeroVec⟩

noncomputable def bitVec1k0PureMeasureActualSparseRecoveryRegionBridge :
    PMF (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  PMF.pure bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge

noncomputable def bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge :
    Finset (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  {bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge}

noncomputable local instance exactVisiblePostSwitchSurfaceBitVec1k0DecidableEqBridge :
    DecidableEq (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  Classical.decEq _

private theorem bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge_filter_card :
    ({x ∈ bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge
        | x = bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge}).card = 1 := by
  apply Finset.card_eq_one.mpr
  refine ⟨bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge, ?_⟩
  simp [bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge,
    bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge]

def zeroBitVec1ToBitVec0ActualSparseRecoveryThresholdVisibleBudgetBridge :
    BitVec 1 → BitVec 0 := fun _ => zeroVec

def zeroBitVec3ToBitVec1ActualSparseRecoveryThresholdVisibleBudgetBridge :
    BitVec 3 → BitVec 1 := fun _ => zeroVec

local instance exactVisiblePostSwitchSurfaceBitVec3k0NonemptyThresholdVisibleBudgetBridge :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 3) 0) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

noncomputable def bitVec3k0UniformMeasureActualSparseRecoveryThresholdVisibleBudgetBridge :
    PMF (ExactVisiblePostSwitchSurface (BitVec 3) 0) :=
  PMF.uniformOfFintype _

end Mettapedia.Computability.PNP.CruxSynthesisRegression
