import Mettapedia.Computability.PNP.V14PublicReadToy

/-!
# PNP v14 toy conditional endgame

This module assembles the v14 toy's separation-shaped endpoint.  It keeps the
result conditional: the remaining mathematical inputs are StarSW hardness and
the three analytic frontier fields.  The self-reduction upper side is supplied
by the explicit P=NP-side SAT-decider object from `V14PublicReadToy`.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

def v14ToyEndgameAnalyticFrontier
    (safeQSSM : SafeQSSMFrontier)
    (boundedGaugeIncidence : BoundedGaugeIncidenceFrontier)
    (boundaryMixing : BoundaryMixingFrontier) :
    V14ToyAnalyticFrontier where
  safeQSSM := safeQSSM
  boundedGaugeIncidence := boundedGaugeIncidence
  boundaryMixing := boundaryMixing

def v14ToyEndgameTargetBlocks (D : V14ToyPNPSATDecider) : Nat :=
  v14ToySelfReductionDecoderCost D + 1

def v14ToyEndgameLowerFramework
    (D : V14ToyPNPSATDecider) :
    CompressionLowerFramework where
  Predictor := Unit
  short := fun _ => True
  uLocal := fun _ => False
  pivotSuccess := fun _ => 1
  tupleSuccess := fun _ => 1
  halfBudget := 0
  halfPlusSlackBudget := 0
  smallSuccessBudget := 0
  targetBlocks := v14ToyEndgameTargetBlocks D
  etaTimes := v14ToyLinearEtaTimes 1
  kpolyAt := v14ToyConstantDecoderKpolyAt D
  productSmallSuccess := by
    intro A hPivot
    exact hPivot
  compressionFromSuccess := by
    intro hsmall
    have hbad : (1 : Nat) ≤ 0 := hsmall () trivial
    exact False.elim (Nat.not_succ_le_zero 0 hbad)

def v14ToyEndgameKernelNeutrality
    (D : V14ToyPNPSATDecider) :
    CompressionKernelNeutrality (v14ToyEndgameLowerFramework D) where
  exactLocalHalfBound := by
    intro A hLocal
    cases hLocal
  halfBudget_le_starBudget := Nat.le_refl 0

def v14ToyEndgameConstantDecoderRegime
    (D : V14ToyPNPSATDecider) :
    V14ToyConstantDecoderRegime
      (v14ToyEndgameLowerFramework D) D where
  eta := 1
  kpolyAt_eq := rfl
  etaTimes_eq := rfl
  floor_dominates_decoder := by
    simp [v14ToyEndgameLowerFramework, v14ToyEndgameTargetBlocks]

def v14ToyEndgameParameterRecord
    (D : V14ToyPNPSATDecider)
    (starSWHardness :
      CompressionStarSWHardness (v14ToyEndgameLowerFramework D))
    (safeQSSM : SafeQSSMFrontier)
    (boundedGaugeIncidence : BoundedGaugeIncidenceFrontier)
    (boundaryMixing : BoundaryMixingFrontier) :
    ParameterRecord
      (v14ToyLockedInterface
        (v14ToyEndgameAnalyticFrontier
          safeQSSM boundedGaugeIncidence boundaryMixing)) where
  fixedGapBudget := 0
  phaseABudget := by
    change (1 / 2 : Rat) * v14ToyTelescoping.derivativeSum ≤ 0
    norm_num [v14ToyLockedInterface, v14ToyEvidenceSpineBound,
      v14ToyTelescoping, DerivativeTelescoping.derivativeSum]
  epsSmall := by
    norm_num [v14ToyLockedInterface, v14ToyEpsMix]
  lowerFramework := v14ToyEndgameLowerFramework D
  kernelNeutrality := v14ToyEndgameKernelNeutrality D
  starSWHardness := starSWHardness
  selfReductionUpper :=
    v14Toy_selfReductionUpperHypothesis_givenPNP D
      (v14ToyEndgameConstantDecoderRegime D)

/--
Conditional endgame for the v14 toy only.  It assembles `UpperLowerClash` from
StarSW hardness, the three analytic frontier fields, and the explicit P=NP-side
SAT decider used by the self-reduction upper side.  This is not a proof of
`P != NP`, does not identify the toy with the manuscript's real SAT ensemble,
and does not prove that the four irreducible inputs are satisfiable.
-/
theorem v14Toy_conditionalSeparation_of_starSW_and_analyticFrontier
    (D : V14ToyPNPSATDecider)
    (starSWHardness :
      CompressionStarSWHardness (v14ToyEndgameLowerFramework D))
    (safeQSSM : SafeQSSMFrontier)
    (boundedGaugeIncidence : BoundedGaugeIncidenceFrontier)
    (boundaryMixing : BoundaryMixingFrontier) :
    UpperLowerClash
      (v14ToyLockedInterface
        (v14ToyEndgameAnalyticFrontier
          safeQSSM boundedGaugeIncidence boundaryMixing))
      (v14ToyEndgameParameterRecord D starSWHardness
        safeQSSM boundedGaugeIncidence boundaryMixing) :=
  (v14Toy_reduction_uses_exact_analytic_frontier_givenPNP
    (v14ToyEndgameAnalyticFrontier
      safeQSSM boundedGaugeIncidence boundaryMixing)
    (v14ToyEndgameParameterRecord D starSWHardness
      safeQSSM boundedGaugeIncidence boundaryMixing)
    D
    (v14ToyEndgameConstantDecoderRegime D)).conclusion

inductive V14ToyEndgameLedgerStatus where
  | pnpDeciderHypothesis
  | irreducibleInput
  | constructionProved
  | constructionProvedGivenPNP
  | derivedMechanical
deriving DecidableEq, Repr

structure V14ToyEndgameLedgerRow where
  item : String
  status : V14ToyEndgameLedgerStatus
  checkedName : String
  note : String
deriving Repr

def v14ToyEndgameHypothesisLedger :
    List V14ToyEndgameLedgerRow := [
  {
    item := "pnpDecider"
    status := .pnpDeciderHypothesis
    checkedName := "V14ToyPNPSATDecider"
    note := "Explicit P=NP-side SAT-decider object used only for the upper self-reduction."
  },
  {
    item := "starSWHardness"
    status := .irreducibleInput
    checkedName := "CompressionStarSWHardness (v14ToyEndgameLowerFramework D)"
    note := "The residual SW-shaped transfer from local-neutral predictors to short predictors."
  },
  {
    item := "safeQSSM"
    status := .irreducibleInput
    checkedName := "SafeQSSMFrontier"
    note := "The safe-buffer analytic frontier field."
  },
  {
    item := "boundedGaugeIncidence"
    status := .irreducibleInput
    checkedName := "BoundedGaugeIncidenceFrontier"
    note := "The gauge-incidence analytic frontier field."
  },
  {
    item := "boundaryMixing"
    status := .irreducibleInput
    checkedName := "BoundaryMixingFrontier"
    note := "The boundary-mixing analytic frontier field."
  }
]

theorem v14ToyEndgameHypothesisLedger_exact :
    v14ToyEndgameHypothesisLedger.map (fun row => row.item) =
        ["pnpDecider", "starSWHardness", "safeQSSM",
          "boundedGaugeIncidence", "boundaryMixing"] ∧
      v14ToyEndgameHypothesisLedger.map (fun row => row.status) =
        [V14ToyEndgameLedgerStatus.pnpDeciderHypothesis,
          V14ToyEndgameLedgerStatus.irreducibleInput,
          V14ToyEndgameLedgerStatus.irreducibleInput,
          V14ToyEndgameLedgerStatus.irreducibleInput,
          V14ToyEndgameLedgerStatus.irreducibleInput] := by
  constructor <;> rfl

def v14ToyEndgameMechanicalLedger :
    List V14ToyEndgameLedgerRow := [
  {
    item := "singleMessage"
    status := .constructionProved
    checkedName := "v14ToySingleMessage"
    note := "Structural interface field supplied by the toy construction."
  },
  {
    item := "noPublicTargetTags"
    status := .constructionProved
    checkedName := "v14ToyNoPublicTargetTags"
    note := "Structural interface field supplied by the toy construction."
  },
  {
    item := "atomCompleteness"
    status := .constructionProved
    checkedName := "v14ToyAtomCompleteness"
    note := "CD-ENF atom-completeness field supplied by the toy construction."
  },
  {
    item := "gaugeFaithfulness"
    status := .constructionProved
    checkedName := "v14ToyGaugeFaithfulness"
    note := "Gauge-faithfulness field supplied by the toy construction."
  },
  {
    item := "gaugePredicateTotal"
    status := .constructionProved
    checkedName := "v14ToyInterfaceHiddenGaugeProduct"
    note := "Hidden-gauge product field supplied by the toy construction."
  },
  {
    item := "admissibleHistories"
    status := .constructionProved
    checkedName := "v14ToyHistory_admissible"
    note := "Admissible-history field supplied by the toy construction."
  },
  {
    item := "publicReadCDENF"
    status := .constructionProved
    checkedName := "v14ToyInterfaceBattery_test8"
    note := "Public reads normalize to target-blind neutral evidence or charged leaves."
  },
  {
    item := "lowerFramework"
    status := .derivedMechanical
    checkedName := "v14ToyEndgameLowerFramework"
    note := "Concrete finite lower-side framework used by the toy endgame."
  },
  {
    item := "kernelNeutrality"
    status := .derivedMechanical
    checkedName := "v14ToyEndgameKernelNeutrality"
    note := "Concrete lower-side kernel-neutrality payload."
  },
  {
    item := "selfReductionUpper"
    status := .constructionProvedGivenPNP
    checkedName := "v14Toy_selfReductionUpperHypothesis_givenPNP"
    note := "Self-reduction upper side discharged from the explicit SAT decider."
  },
  {
    item := "parameterRecord"
    status := .derivedMechanical
    checkedName := "v14ToyEndgameParameterRecord"
    note := "Numeric and derived `ParameterRecord` payload built from the theorem inputs."
  }
]

theorem v14ToyEndgameMechanicalLedger_discharged :
    v14ToyEndgameMechanicalLedger.map (fun row => row.status) =
      [V14ToyEndgameLedgerStatus.constructionProved,
        V14ToyEndgameLedgerStatus.constructionProved,
        V14ToyEndgameLedgerStatus.constructionProved,
        V14ToyEndgameLedgerStatus.constructionProved,
        V14ToyEndgameLedgerStatus.constructionProved,
        V14ToyEndgameLedgerStatus.constructionProved,
        V14ToyEndgameLedgerStatus.constructionProved,
        V14ToyEndgameLedgerStatus.derivedMechanical,
        V14ToyEndgameLedgerStatus.derivedMechanical,
        V14ToyEndgameLedgerStatus.constructionProvedGivenPNP,
        V14ToyEndgameLedgerStatus.derivedMechanical] := by
  rfl

def v14ToyEndgameLedger : List V14ToyEndgameLedgerRow :=
  v14ToyEndgameHypothesisLedger ++ v14ToyEndgameMechanicalLedger

theorem v14ToyEndgameLedger_length :
    v14ToyEndgameLedger.length = 16 := by
  rfl

def v14ToyEndgameStatement : String :=
  "For the v14 toy construction, the separation-shaped clash (UpperLowerClash) follows from exactly StarSW hardness and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing, with self-reduction-upper discharged given P=NP and all structural interface fields construction-proved; these four are the irreducible content."

end Mettapedia.Computability.PNP
