import Mettapedia.Computability.PNP.V13InterfaceBattery

/-!
# PNP v14 construction-side public-read toy

This module instantiates the v13 public-input battery on a small finite
locked/gauge read vocabulary.  The full public lock syntax may determine the
target at the semantic level, but the primitive read interface exposes only a
target-blind skeleton read as neutral.  Safe-buffer and quotient-style reads
normalize to charged leaves.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-! ## A small locked/gauge public-read vocabulary -/

structure V14ToyPublic where
  lockSyntax : Bool
deriving DecidableEq, Repr

inductive V14ToyNeutral where
  | skeleton
deriving DecidableEq, Repr

inductive V14ToySafe where
  | lockRead
  | bufferProbe
deriving DecidableEq, Repr

inductive V14ToyGauge where
  | rawWitness
  | hiddenGauge
deriving DecidableEq, Repr

inductive V14ToyPublicSymbol where
  | skeleton
  | safeBuffer
  | quotient
deriving DecidableEq, Repr

def v14ToyPublicReadTargetBlind : V14ToyPublicSymbol -> Prop
  | .skeleton => True
  | .safeBuffer => False
  | .quotient => False

def v14ToyReadPublic :
    V14ToyPublicSymbol -> RawEvidence V14ToyNeutral V14ToySafe V14ToyGauge
  | .skeleton => .neutral .skeleton
  | .safeBuffer => .safe .bufferProbe
  | .quotient =>
      .disj
        (.conj (.gauge .rawWitness) (.gauge .hiddenGauge))
        (.conj (.gauge .hiddenGauge) (.gauge .rawWitness))

theorem v14ToyPublicRead_neutralOnly_targetBlind :
    PublicReadNeutralOnlyTargetBlind
      v14ToyReadPublic v14ToyPublicReadTargetBlind := by
  intro theta hNeutral
  cases theta <;>
    simp [v14ToyReadPublic, v14ToyPublicReadTargetBlind,
      NormalEvidenceOnlyNeutralLeaves, CDENF] at hNeutral ⊢

def v14ToyPublicReadInterface :
    PublicReadCDENFInterface
      V14ToyPublicSymbol V14ToyNeutral V14ToySafe V14ToyGauge where
  readPublic := v14ToyReadPublic
  targetBlind := v14ToyPublicReadTargetBlind
  neutralOnly_targetBlind := v14ToyPublicRead_neutralOnly_targetBlind

theorem v14ToyPublicRead_decomposes
    (theta : V14ToyPublicSymbol) :
    (NormalEvidenceOnlyNeutralLeaves
          (CDENF (v14ToyPublicReadInterface.readPublic theta)) ∧
        v14ToyPublicReadInterface.targetBlind theta) ∨
      NormalEvidenceHasChargedLeaf
        (CDENF (v14ToyPublicReadInterface.readPublic theta)) :=
  public_read_cdenf_normalizes_neutral_or_charged
    v14ToyPublicReadInterface theta

theorem v14ToyPublicRead_skeleton_is_neutral_targetBlind :
    NormalEvidenceOnlyNeutralLeaves
        (CDENF (v14ToyReadPublic .skeleton)) ∧
      v14ToyPublicReadTargetBlind .skeleton := by
  simp [v14ToyReadPublic, v14ToyPublicReadTargetBlind,
    NormalEvidenceOnlyNeutralLeaves, CDENF]

theorem v14ToyPublicRead_safeBuffer_has_charged_leaf :
    NormalEvidenceHasChargedLeaf
      (CDENF (v14ToyReadPublic .safeBuffer)) := by
  simp [v14ToyReadPublic, NormalEvidenceHasChargedLeaf, CDENF]

theorem v14ToyPublicRead_quotient_has_charged_leaf :
    NormalEvidenceHasChargedLeaf
      (CDENF (v14ToyReadPublic .quotient)) := by
  simp [v14ToyReadPublic, NormalEvidenceHasChargedLeaf, CDENF]

/-! ## A finite toy interface that runs the battery -/

def v14ToyPublicInput (omega : Bool) : V14ToyPublic where
  lockSyntax := omega

def v14ToyNeutralSkeleton (_omega : Bool) : Unit :=
  ()

def v14ToySemantics :
    EvidenceSemantics Bool V14ToyNeutral V14ToySafe V14ToyGauge where
  neutralSat := fun _ _ => True
  safeSat := fun _ _ => True
  gaugeSat := fun _ _ => True

def v14ToyObserverEvidenceInterface :
    ObserverEvidenceInterface
      Bool V14ToyPublic Unit Unit V14ToyNeutral V14ToySafe V14ToyGauge where
  semantics := v14ToySemantics
  publicInput := v14ToyPublicInput
  evalObserver := fun _ _ => ()
  observerToEvidence := fun _ _ => .top
  observerToEvidence_sat := by
    intro observer output
    funext omega
    cases output
    simp [EvidenceSemantics.SatRaw]

def v14ToyLockedInterface :
    GaugeBufferedLockedInterface
      Bool V14ToyPublic V14ToyNeutral V14ToySafe V14ToyGauge Bool Unit Unit Unit
      Unit Unit Unit Unit Unit where
  law := toyV13Law
  target := publicNeutralityToyB
  publicInput := v14ToyPublicInput
  neutralSkeleton := v14ToyNeutralSkeleton
  oppositeSupport := publicNeutralityToySupport
  transcript := toyV13Transcript
  observerBit := toyV13Observer
  phaseA := toyV13EvidenceSpineBound
  semantics := v14ToySemantics
  observerEvidence := v14ToyObserverEvidenceInterface
  historyField := toyLedgerHistoryField
  pivotSummary := toyLedgerPivot
  epsMix := 0
  safeCost := fun _ => 0
  safeBudget := 0
  gaugeIncidence := fun _ => 0
  gaugeBound := 0
  singleMessage := by
    intro w0 w1 hPublic
    exact congrArg V14ToyPublic.lockSyntax hPublic
  hiddenGaugeProduct := by
    intro gamma omega
    trivial
  noPublicTargetTags := toyLedger_noPublicTargetTags
  atomCompleteness := by
    intro E
    exact CDENF_semantics v14ToySemantics E
  gaugeFaithfulness := by
    intro gamma
    rfl
  safeQSSM := by
    intro q
    norm_num
  boundedGaugeIncidence := by
    intro gamma
    norm_num
  boundaryMixing := toyLedger_boundaryMixing
  admissibleHistories := toyLedger_admissibleHistory

def v14ToyInterfaceBattery :
    V13InterfaceConsistencyBattery
      v14ToyLockedInterface v14ToyPublicReadInterface :=
  v13_interfaceConsistencyBattery
    v14ToyLockedInterface v14ToyPublicReadInterface

theorem v14ToyInterfaceBattery_test8 :
    ∀ theta,
      (NormalEvidenceOnlyNeutralLeaves
          (CDENF (v14ToyPublicReadInterface.readPublic theta)) ∧
          v14ToyPublicReadInterface.targetBlind theta) ∨
        NormalEvidenceHasChargedLeaf
          (CDENF (v14ToyPublicReadInterface.readPublic theta)) :=
  v14ToyInterfaceBattery.test8_full_public_read_decomposes

/-! ## Construction-side ledger -/

inductive V14ConstructionLedgerStatus where
  | constructionProved
  | carriedAsAssumption
deriving DecidableEq, Repr

structure V14ConstructionLedgerRow where
  item : String
  status : V14ConstructionLedgerStatus
  checkedName : String
  note : String
deriving Repr

def v14ToyConstructionLedger : List V14ConstructionLedgerRow := [
  {
    item := "field singleMessage"
    status := .constructionProved
    checkedName := "v14ToyLockedInterface.singleMessage"
    note := "The toy lockSyntax field fixes the target on full-public equality."
  },
  {
    item := "field hiddenGaugeProduct"
    status := .constructionProved
    checkedName := "v14ToyLockedInterface.hiddenGaugeProduct"
    note := "Trivial finite toy gauge semantics; nontrivial product law remains a real-ensemble obligation."
  },
  {
    item := "field noPublicTargetTags"
    status := .constructionProved
    checkedName := "v14ToyLockedInterface.noPublicTargetTags"
    note := "Neutral skeleton is constant, pair-neutral, and not target-sufficient."
  },
  {
    item := "field atomCompleteness"
    status := .constructionProved
    checkedName := "v14ToyLockedInterface.atomCompleteness"
    note := "All toy raw evidence is normalized by CDENF_semantics."
  },
  {
    item := "field gaugeFaithfulness"
    status := .constructionProved
    checkedName := "v14ToyLockedInterface.gaugeFaithfulness"
    note := "Toy gauge leaves preserve their gauge semantics; real quotient algebra remains separate."
  },
  {
    item := "field safeQSSM"
    status := .constructionProved
    checkedName := "v14ToyLockedInterface.safeQSSM"
    note := "Toy safe costs are zero; real max-qSSM remains a real-ensemble obligation."
  },
  {
    item := "field boundedGaugeIncidence"
    status := .constructionProved
    checkedName := "v14ToyLockedInterface.boundedGaugeIncidence"
    note := "Toy gauge incidence is zero."
  },
  {
    item := "field boundaryMixing"
    status := .constructionProved
    checkedName := "v14ToyLockedInterface.boundaryMixing"
    note := "The toy pivot is constant and has exact half success."
  },
  {
    item := "field admissibleHistories"
    status := .constructionProved
    checkedName := "v14ToyLockedInterface.admissibleHistories"
    note := "The toy history field is constant and target-balanced."
  },
  {
    item := "test 1 same full public no opposite"
    status := .constructionProved
    checkedName := "v14ToyInterfaceBattery.test1_sameFullPublic_noOpposite"
    note := "Derived from toy singleMessage."
  },
  {
    item := "test 2 neutral atoms cannot generate target"
    status := .constructionProved
    checkedName := "v14ToyInterfaceBattery.test2_neutral_generates_target_contradiction"
    note := "Derived from toy neutral-skeleton non-sufficiency."
  },
  {
    item := "test 3 public-bit derivative mass"
    status := .constructionProved
    checkedName := "v14ToyInterfaceBattery.test3_publicBit_derivative_mass_ge_one"
    note := "Inherited from the finite red-team theorem."
  },
  {
    item := "test 4 measurable conditioning obstruction"
    status := .constructionProved
    checkedName := "v14ToyInterfaceBattery.test4_measurable_not_admissible"
    note := "Inherited from the finite red-team theorem."
  },
  {
    item := "test 5 boundary non-sufficiency"
    status := .constructionProved
    checkedName := "v14ToyInterfaceBattery.test5_boundary_mixing_blocks_pivot_sufficiency"
    note := "Derived from toy boundaryMixing and epsMix = 0."
  },
  {
    item := "test 6 no opaque run atom"
    status := .constructionProved
    checkedName := "v14ToyInterfaceBattery.test6_no_opaque_run_atom"
    note := "RawEvidence has no observer-output constructor and observers expand through observerToEvidence."
  },
  {
    item := "test 7 neutral skeleton not sufficient"
    status := .constructionProved
    checkedName := "v14ToyInterfaceBattery.test7_neutral_skeleton_not_target_sufficient"
    note := "The toy neutral skeleton is constant."
  },
  {
    item := "test 8 full public read decomposition"
    status := .constructionProved
    checkedName := "v14ToyInterfaceBattery_test8"
    note := "Only skeleton reads are neutral-only; safeBuffer and quotient reads have charged leaves."
  }
]

theorem v14ToyConstructionLedger_length :
    v14ToyConstructionLedger.length = 17 := by
  rfl

theorem v14ToyConstructionLedger_test8_proved :
    (v14ToyConstructionLedger.get ⟨16, by decide⟩).status =
      V14ConstructionLedgerStatus.constructionProved := by
  rfl

end Mettapedia.Computability.PNP
