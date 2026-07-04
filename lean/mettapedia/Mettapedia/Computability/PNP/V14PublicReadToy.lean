import Mettapedia.Computability.PNP.V13ConditionalClash
import Mettapedia.Computability.PNP.V13InterfaceBattery

/-!
# PNP v14 locked/gauge public-read toy

This module upgrades the v14 public-read toy to a small locked/gauge
construction.  The full public lock syntax has two Boolean coordinates and
forces the message by their xor; neither coordinate alone is a public target
tag.  The raw witness/gauge layer has a genuine gauge orbit, and quotient-style
public reads normalize to charged raw-gauge support.

The structural interface fields are construction theorems for this toy.  The
three quantitative fields are packaged as the single analytic frontier
`V14ToyAnalyticFrontier`.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-! ## A four-world locked public syntax -/

abbrev V14ToyWorld := Bool × Bool

structure V14ToyPublic where
  lockLeft : Bool
  lockRight : Bool
deriving DecidableEq, Repr

def v14ToyTarget (omega : V14ToyWorld) : Bool :=
  omega.1 ^^ omega.2

def v14ToyPublicInput (omega : V14ToyWorld) : V14ToyPublic where
  lockLeft := omega.1
  lockRight := omega.2

def v14ToyMessageOfPublic (Y : V14ToyPublic) : Bool :=
  Y.lockLeft ^^ Y.lockRight

theorem v14ToyPublicMessage_eq_target (omega : V14ToyWorld) :
    v14ToyMessageOfPublic (v14ToyPublicInput omega) = v14ToyTarget omega :=
  rfl

theorem v14ToySingleMessage :
    ∀ w0 w1 : V14ToyWorld,
      v14ToyPublicInput w0 = v14ToyPublicInput w1 ->
        v14ToyTarget w0 = v14ToyTarget w1 := by
  intro w0 w1 hPublic
  cases w0 with
  | mk a0 b0 =>
      cases w1 with
      | mk a1 b1 =>
          simp [v14ToyPublicInput, v14ToyTarget] at hPublic ⊢
          rcases hPublic with ⟨ha, hb⟩
          rw [ha, hb]

/-! ## Locked verifier, message readout, and gauge orbit -/

structure V14ToyWitness where
  rawWitness : Bool
  hiddenGauge : Bool
  quotient : Bool
  message : Bool
deriving DecidableEq, Repr

def v14ToyGaugeEq (W : V14ToyWitness) : Prop :=
  W.quotient = W.rawWitness ^^ W.hiddenGauge

def v14ToyLockedVerifier (Y : V14ToyPublic) (W : V14ToyWitness) : Prop :=
  v14ToyGaugeEq W ∧ W.message = v14ToyMessageOfPublic Y

def v14ToyMessageReadout (W : V14ToyWitness) : Bool :=
  W.message

def v14ToyGaugeAction (s : Bool) (W : V14ToyWitness) : V14ToyWitness :=
  { W with
    rawWitness := W.rawWitness ^^ s
    hiddenGauge := W.hiddenGauge ^^ s }

theorem v14ToyVerifier_singleMessage
    (Y : V14ToyPublic) (W W' : V14ToyWitness)
    (hW : v14ToyLockedVerifier Y W) (hW' : v14ToyLockedVerifier Y W') :
    v14ToyMessageReadout W = v14ToyMessageReadout W' :=
  hW.2.trans hW'.2.symm

theorem v14ToyGaugeEquation_preserved
    (W : V14ToyWitness) (s : Bool) (hW : v14ToyGaugeEq W) :
    v14ToyGaugeEq (v14ToyGaugeAction s W) := by
  cases W with
  | mk x g z m =>
      cases x <;> cases g <;> cases z <;> cases m <;> cases s <;>
        simp [v14ToyGaugeEq, v14ToyGaugeAction] at hW ⊢

def v14ToyGaugeProbability (E : Bool -> Prop) [DecidablePred E] : Rat :=
  (Fintype.card {g : Bool // E g} : Rat) / 2

def v14ToyGaugeUnsupported (charged : Bool) : Prop :=
  charged = false

theorem v14ToyHiddenGaugeProduct
    (charged : Bool) (_hUnsupported : v14ToyGaugeUnsupported charged)
    (gamma : Bool) :
    v14ToyGaugeProbability (fun g => g = gamma) = (1 / 2 : Rat) := by
  cases gamma <;> norm_num [v14ToyGaugeProbability]

/-! ## Public-read vocabulary and quotient gauge faithfulness -/

inductive V14ToyNeutral where
  | skeleton
  | lockLeft
  | lockRight
deriving DecidableEq, Repr

inductive V14ToySafe where
  | bufferProbe
deriving DecidableEq, Repr

inductive V14ToyGauge where
  | rawWitness
  | hiddenGauge
deriving DecidableEq, Repr

inductive V14ToyPublicSymbol where
  | skeleton
  | lockLeft
  | lockRight
  | safeBuffer
  | quotient
deriving DecidableEq, Repr

inductive V14ToyPublicCoordinate where
  | lockLeft
  | lockRight
deriving DecidableEq, Repr

def v14ToyPublicCoordinateValue :
    V14ToyPublicCoordinate -> V14ToyPublic -> Bool
  | .lockLeft, Y => Y.lockLeft
  | .lockRight, Y => Y.lockRight

def v14ToyPublicReadTargetBlind : V14ToyPublicSymbol -> Prop
  | .skeleton | .lockLeft | .lockRight => True
  | .safeBuffer | .quotient => False

def v14ToyReadPublic :
    V14ToyPublicSymbol -> RawEvidence V14ToyNeutral V14ToySafe V14ToyGauge
  | .skeleton => .neutral .skeleton
  | .lockLeft => .neutral .lockLeft
  | .lockRight => .neutral .lockRight
  | .safeBuffer => .safe .bufferProbe
  | .quotient =>
      .disj
        (.conj (.gauge .rawWitness) (.gauge .hiddenGauge))
        (.conj (.gauge .hiddenGauge) (.gauge .rawWitness))

def NormalEvidenceMentionsGauge
    {Neutral : Type*} {Safe : Type*} {Gauge : Type*}
    (needle : Gauge) :
    NormalEvidence Neutral Safe Gauge -> Prop
  | .N _ => False
  | .S _ => False
  | .G gamma => gamma = needle
  | .top => False
  | .bot => False
  | .conj E F =>
      NormalEvidenceMentionsGauge needle E ∨
        NormalEvidenceMentionsGauge needle F
  | .disj E F =>
      NormalEvidenceMentionsGauge needle E ∨
        NormalEvidenceMentionsGauge needle F
  | .neg E => NormalEvidenceMentionsGauge needle E

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

theorem v14ToyPublicRead_lockLeft_is_neutral_targetBlind :
    NormalEvidenceOnlyNeutralLeaves
        (CDENF (v14ToyReadPublic .lockLeft)) ∧
      v14ToyPublicReadTargetBlind .lockLeft := by
  simp [v14ToyReadPublic, v14ToyPublicReadTargetBlind,
    NormalEvidenceOnlyNeutralLeaves, CDENF]

theorem v14ToyPublicRead_lockRight_is_neutral_targetBlind :
    NormalEvidenceOnlyNeutralLeaves
        (CDENF (v14ToyReadPublic .lockRight)) ∧
      v14ToyPublicReadTargetBlind .lockRight := by
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

theorem v14ToyQuotientRead_exposes_rawGaugeSupport :
    NormalEvidenceMentionsGauge V14ToyGauge.rawWitness
        (CDENF (v14ToyReadPublic .quotient)) ∧
      NormalEvidenceMentionsGauge V14ToyGauge.hiddenGauge
        (CDENF (v14ToyReadPublic .quotient)) := by
  simp [NormalEvidenceMentionsGauge, v14ToyReadPublic, CDENF]

theorem v14ToyNoPublicCoordinateDeterminesTarget :
    ∀ coord : V14ToyPublicCoordinate,
      ¬ ∃ f : Bool -> Bool,
        ∀ omega : V14ToyWorld,
          v14ToyTarget omega =
            f (v14ToyPublicCoordinateValue coord (v14ToyPublicInput omega)) := by
  intro coord h
  rcases h with ⟨f, hf⟩
  cases coord
  · have h00 := hf (false, false)
    have h01 := hf (false, true)
    simp [v14ToyTarget, v14ToyPublicInput, v14ToyPublicCoordinateValue] at h00 h01
    have hcontra : (false : Bool) = true := h00.symm.trans h01
    cases hcontra
  · have h00 := hf (false, false)
    have h10 := hf (true, false)
    simp [v14ToyTarget, v14ToyPublicInput, v14ToyPublicCoordinateValue] at h00 h10
    have hcontra : (false : Bool) = true := h00.symm.trans h10
    cases hcontra

/-! ## Finite phase-A and admissible-history bookkeeping for the toy -/

def v14ToyLaw : FiniteRationalLaw V14ToyWorld where
  weight := fun _ => (1 / 4 : Rat)
  nonnegative := by
    intro omega
    norm_num
  total_weight := by
    rw [Finset.sum_const]
    simp [V14ToyWorld]

def v14ToyTranscript (_omega : V14ToyWorld) : Unit :=
  ()

def v14ToyObserver (_t : Unit) : Bool :=
  false

theorem v14Toy_gap_eq_zero :
    Gap v14ToyLaw v14ToyTarget v14ToyTranscript v14ToyObserver = (0 : Rat) := by
  simp [Gap, halfAbsDiff, FiniteRationalLaw.conditionalProb,
    FiniteRationalLaw.eventWeight, v14ToyLaw, v14ToyTarget, v14ToyObserver,
    V14ToyWorld]

def v14ToyStaticCapture :
    StaticPairwiseCapture v14ToyLaw v14ToyTarget
      v14ToyTranscript v14ToyObserver Unit where
  pairWeight := fun _ => 0
  pairNonnegative := by
    intro p
    norm_num
  left := fun _ => (false, false)
  right := fun _ => (false, true)
  opposite := by
    intro p
    exact ⟨rfl, rfl⟩

theorem v14ToyStaticCapture_sepMass :
    v14ToyStaticCapture.sepMass = 0 := by
  norm_num [StaticPairwiseCapture.sepMass, couplingSepMass,
    v14ToyStaticCapture, v14ToyTranscript]

theorem v14ToyStaticCapture_capturesGap :
    v14ToyStaticCapture.CapturesGap := by
  rw [StaticPairwiseCapture.CapturesGap, v14Toy_gap_eq_zero,
    v14ToyStaticCapture_sepMass]
  norm_num

def v14ToyTelescoping : DerivativeTelescoping Unit Unit where
  stageFinite := inferInstance
  branchFinite := inferInstance
  finalWeight := 1
  derivative := fun _ _ => 0
  derivativeNonnegative := by
    intro r h
    norm_num
  telescopes := by
    norm_num

def v14ToyEvidenceSpineBound :
    EvidenceSpineBound v14ToyLaw v14ToyTarget v14ToyTranscript
      v14ToyObserver Unit Unit Unit where
  capture := v14ToyStaticCapture
  capturesGap := v14ToyStaticCapture_capturesGap
  telescoping := v14ToyTelescoping
  sep_le_derivativeSum := by
    rw [v14ToyStaticCapture_sepMass]
    norm_num [DerivativeTelescoping.derivativeSum, v14ToyTelescoping]

def v14ToyNeutralSkeleton (_omega : V14ToyWorld) : Unit :=
  ()

def v14ToyOppositeSupport (w0 w1 : V14ToyWorld) : Prop :=
  v14ToyTarget w0 = false ∧ v14ToyTarget w1 = true

theorem v14ToyHasOppositePair :
    HasMessageOppositePair v14ToyOppositeSupport v14ToyTarget :=
  ⟨(false, false), (false, true), ⟨rfl, rfl⟩, rfl, rfl⟩

theorem v14ToyNoPublicTargetTags :
    PairNeutral v14ToyOppositeSupport v14ToyNeutralSkeleton ∧
      HasMessageOppositePair v14ToyOppositeSupport v14ToyTarget ∧
        ¬ ∃ f : Unit -> Bool,
          ∀ omega, v14ToyTarget omega = f (v14ToyNeutralSkeleton omega) := by
  refine ⟨?neutral, v14ToyHasOppositePair, ?notSuff⟩
  · intro w0 w1 h
    rfl
  · intro h
    rcases h with ⟨f, hf⟩
    have h00 := hf (false, false)
    have h01 := hf (false, true)
    simp [v14ToyTarget, v14ToyNeutralSkeleton] at h00 h01
    have hcontra : (false : Bool) = true := h00.symm.trans h01
    cases hcontra

theorem v14ToyTarget_true_card :
    Fintype.card {omega : V14ToyWorld // v14ToyTarget omega = true} = 2 := by
  let e : {omega : V14ToyWorld // v14ToyTarget omega = true} ≃ Bool :=
    { toFun := fun omega => omega.val.1
      invFun := fun b => ⟨(b, !b), by cases b <;> rfl⟩
      left_inv := by
        intro omega
        cases omega with
        | mk val h =>
            cases val with
            | mk a b =>
                cases a <;> cases b <;> simp [v14ToyTarget] at h ⊢
      right_inv := by
        intro b
        cases b <;> rfl }
  rw [← Fintype.card_bool]
  exact Fintype.card_congr e

theorem v14ToyTarget_true_left_card :
    Fintype.card {omega : V14ToyWorld // true = v14ToyTarget omega} = 2 := by
  let e : {omega : V14ToyWorld // true = v14ToyTarget omega} ≃
      {omega : V14ToyWorld // v14ToyTarget omega = true} :=
    { toFun := fun omega => ⟨omega.val, omega.property.symm⟩
      invFun := fun omega => ⟨omega.val, omega.property.symm⟩
      left_inv := by
        intro omega
        cases omega
        rfl
      right_inv := by
        intro omega
        cases omega
        rfl }
  rw [← v14ToyTarget_true_card]
  exact Fintype.card_congr e

theorem v14ToyTarget_false_card :
    Fintype.card {omega : V14ToyWorld // v14ToyTarget omega = false} = 2 := by
  let e : {omega : V14ToyWorld // v14ToyTarget omega = false} ≃ Bool :=
    { toFun := fun omega => omega.val.1
      invFun := fun b => ⟨(b, b), by cases b <;> rfl⟩
      left_inv := by
        intro omega
        cases omega with
        | mk val h =>
            cases val with
            | mk a b =>
                cases a <;> cases b <;> simp [v14ToyTarget] at h ⊢
      right_inv := by
        intro b
        cases b <;> rfl }
  rw [← Fintype.card_bool]
  exact Fintype.card_congr e

theorem v14ToyTarget_balanced :
    BalancedBit v14ToyTarget := by
  unfold BalancedBit globalDecoderSuccess
  rw [v14ToyTarget_true_left_card]
  norm_num [V14ToyWorld]

def v14ToyHistoryField : FiniteSigmaField V14ToyWorld where
  Atom := Unit
  atomDecidable := inferInstance
  atom := fun _ => ()

theorem v14ToyHistory_admissible :
    BalancedBit v14ToyTarget ∧
      BalancedConditioning v14ToyHistoryField v14ToyTarget := by
  constructor
  · exact v14ToyTarget_balanced
  · intro a
    cases a
    unfold FiberTrue FiberFalse
    simp [v14ToyHistoryField]
    rw [v14ToyTarget_true_card, v14ToyTarget_false_card]

def v14ToyPivot (_omega : V14ToyWorld) : Unit :=
  ()

/-! ## Structural interface instance with a named analytic frontier -/

def v14ToySemantics :
    EvidenceSemantics V14ToyWorld V14ToyNeutral V14ToySafe V14ToyGauge where
  neutralSat := fun _ _ => True
  safeSat := fun _ _ => True
  gaugeSat := fun _ _ => True

def v14ToyObserverEvidenceInterface :
    ObserverEvidenceInterface
      V14ToyWorld V14ToyPublic Unit Unit V14ToyNeutral V14ToySafe V14ToyGauge where
  semantics := v14ToySemantics
  publicInput := v14ToyPublicInput
  evalObserver := fun _ _ => ()
  observerToEvidence := fun _ _ => .top
  observerToEvidence_sat := by
    intro observer output
    funext omega
    cases output
    simp [EvidenceSemantics.SatRaw]

def v14ToySafeCost (_q : V14ToySafe) : Rat :=
  0

def v14ToySafeBudget : Rat :=
  0

def v14ToyGaugeIncidence (_gamma : V14ToyGauge) : Nat :=
  0

def v14ToyGaugeBound : Nat :=
  0

def v14ToyEpsMix : Rat :=
  0

structure V14ToyAnalyticFrontier : Prop where
  safeQSSM :
    ∀ q : V14ToySafe,
      0 ≤ v14ToySafeCost q ∧ v14ToySafeCost q ≤ v14ToySafeBudget
  boundedGaugeIncidence :
    ∀ gamma : V14ToyGauge,
      v14ToyGaugeIncidence gamma ≤ v14ToyGaugeBound
  boundaryMixing :
    BoundaryMixingBound v14ToyTarget v14ToyPivot v14ToyEpsMix

theorem v14ToyAtomCompleteness :
    ∀ E : RawEvidence V14ToyNeutral V14ToySafe V14ToyGauge,
      v14ToySemantics.SatNormal (CDENF E) = v14ToySemantics.SatRaw E := by
  intro E
  exact CDENF_semantics v14ToySemantics E

theorem v14ToyGaugeFaithfulness :
    ∀ gamma : V14ToyGauge,
      v14ToySemantics.SatNormal (CDENF (.gauge gamma)) =
        v14ToySemantics.gaugeSat gamma := by
  intro gamma
  rfl

theorem v14ToyInterfaceHiddenGaugeProduct :
    ∀ gamma omega, v14ToySemantics.gaugeSat gamma omega := by
  intro gamma omega
  trivial

def v14ToyLockedInterface (A : V14ToyAnalyticFrontier) :
    GaugeBufferedLockedInterface
      V14ToyWorld V14ToyPublic V14ToyNeutral V14ToySafe V14ToyGauge Unit Unit
      Unit Unit Unit Unit Unit Unit Unit where
  law := v14ToyLaw
  target := v14ToyTarget
  publicInput := v14ToyPublicInput
  neutralSkeleton := v14ToyNeutralSkeleton
  oppositeSupport := v14ToyOppositeSupport
  transcript := v14ToyTranscript
  observerBit := v14ToyObserver
  phaseA := v14ToyEvidenceSpineBound
  semantics := v14ToySemantics
  observerEvidence := v14ToyObserverEvidenceInterface
  historyField := v14ToyHistoryField
  pivotSummary := v14ToyPivot
  epsMix := v14ToyEpsMix
  safeCost := v14ToySafeCost
  safeBudget := v14ToySafeBudget
  gaugeIncidence := v14ToyGaugeIncidence
  gaugeBound := v14ToyGaugeBound
  singleMessage := v14ToySingleMessage
  hiddenGaugeProduct := v14ToyInterfaceHiddenGaugeProduct
  noPublicTargetTags := v14ToyNoPublicTargetTags
  atomCompleteness := v14ToyAtomCompleteness
  gaugeFaithfulness := v14ToyGaugeFaithfulness
  safeQSSM := A.safeQSSM
  boundedGaugeIncidence := A.boundedGaugeIncidence
  boundaryMixing := A.boundaryMixing
  admissibleHistories := v14ToyHistory_admissible

def v14ToyInterfaceBattery (A : V14ToyAnalyticFrontier) :
    V13InterfaceConsistencyBattery
      (v14ToyLockedInterface A) v14ToyPublicReadInterface :=
  v13_interfaceConsistencyBattery
    (v14ToyLockedInterface A) v14ToyPublicReadInterface

theorem v14ToyInterfaceBattery_test8 (A : V14ToyAnalyticFrontier) :
    ∀ theta,
      (NormalEvidenceOnlyNeutralLeaves
          (CDENF (v14ToyPublicReadInterface.readPublic theta)) ∧
          v14ToyPublicReadInterface.targetBlind theta) ∨
        NormalEvidenceHasChargedLeaf
          (CDENF (v14ToyPublicReadInterface.readPublic theta)) :=
  (v14ToyInterfaceBattery A).test8_full_public_read_decomposes

theorem v14Toy_structuralReduction
    (A : V14ToyAnalyticFrontier)
    (P : ParameterRecord (v14ToyLockedInterface A)) :
    UpperLowerClash (v14ToyLockedInterface A) P :=
  v13_upperLowerClash (v14ToyLockedInterface A) P

def v14ToyReductionStatement : String :=
  "With singleMessage, noPublicTargetTags, atomCompleteness, gaugeFaithfulness, hiddenGaugeProduct, and admissibleHistories construction-proved for the v14 toy, the conditional separation reduces to exactly V14ToyAnalyticFrontier.safeQSSM, V14ToyAnalyticFrontier.boundedGaugeIncidence, V14ToyAnalyticFrontier.boundaryMixing, plus ParameterRecord.starSWHardness and ParameterRecord.selfReductionUpper; the Lean conclusion is UpperLowerClash."

/-! ## Construction-side ledger -/

inductive V14ConstructionLedgerStatus where
  | constructionProved
  | carriedAnalyticFrontier
  | provedFromConstructedStructuralInterface
  | provedFromCarriedAnalyticFrontier
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
    checkedName := "v14ToyVerifier_singleMessage / v14ToySingleMessage"
    note := "The public xor lock forces a unique message readout for all satisfying witnesses."
  },
  {
    item := "field hiddenGaugeProduct"
    status := .constructionProved
    checkedName := "v14ToyHiddenGaugeProduct"
    note := "The unsupported one-coordinate hidden gauge law is fair by finite counting."
  },
  {
    item := "field noPublicTargetTags"
    status := .constructionProved
    checkedName := "v14ToyNoPublicTargetTags / v14ToyNoPublicCoordinateDeterminesTarget"
    note := "The neutral skeleton is not target-sufficient, and neither public lock coordinate determines the xor target."
  },
  {
    item := "field atomCompleteness"
    status := .constructionProved
    checkedName := "v14ToyAtomCompleteness"
    note := "CD-ENF for the toy has only neutral, safe-buffer, and gauge leaves."
  },
  {
    item := "field gaugeFaithfulness"
    status := .constructionProved
    checkedName := "v14ToyGaugeFaithfulness / v14ToyQuotientRead_exposes_rawGaugeSupport"
    note := "The quotient read expands to raw witness and hidden-gauge support."
  },
  {
    item := "field safeQSSM"
    status := .carriedAnalyticFrontier
    checkedName := "V14ToyAnalyticFrontier.safeQSSM"
    note := "Quantitative safe-buffer leakage is intentionally carried."
  },
  {
    item := "field boundedGaugeIncidence"
    status := .carriedAnalyticFrontier
    checkedName := "V14ToyAnalyticFrontier.boundedGaugeIncidence"
    note := "Gauge-incidence/rank control is intentionally carried."
  },
  {
    item := "field boundaryMixing"
    status := .carriedAnalyticFrontier
    checkedName := "V14ToyAnalyticFrontier.boundaryMixing"
    note := "Boundary-law mixing is intentionally carried."
  },
  {
    item := "field admissibleHistories"
    status := .constructionProved
    checkedName := "v14ToyHistory_admissible"
    note := "The constant toy history keeps the xor target exactly balanced."
  },
  {
    item := "test 1 same full public no opposite"
    status := .provedFromConstructedStructuralInterface
    checkedName := "v14ToyInterfaceBattery.test1_sameFullPublic_noOpposite"
    note := "Derived from the constructed single-message field."
  },
  {
    item := "test 2 neutral atoms cannot generate target"
    status := .provedFromConstructedStructuralInterface
    checkedName := "v14ToyInterfaceBattery.test2_neutral_generates_target_contradiction"
    note := "Derived from the constructed no-public-target-tags field."
  },
  {
    item := "test 3 public-bit derivative mass"
    status := .provedFromConstructedStructuralInterface
    checkedName := "v14ToyInterfaceBattery.test3_publicBit_derivative_mass_ge_one"
    note := "Inherited from the finite red-team theorem after the toy interface is instantiated."
  },
  {
    item := "test 4 measurable conditioning obstruction"
    status := .provedFromConstructedStructuralInterface
    checkedName := "v14ToyInterfaceBattery.test4_measurable_not_admissible"
    note := "Inherited from the finite red-team theorem after the toy interface is instantiated."
  },
  {
    item := "test 5 boundary non-sufficiency"
    status := .provedFromCarriedAnalyticFrontier
    checkedName := "v14ToyInterfaceBattery.test5_boundary_mixing_blocks_pivot_sufficiency"
    note := "This red-team conclusion uses the carried boundaryMixing field."
  },
  {
    item := "test 6 no opaque run atom"
    status := .provedFromConstructedStructuralInterface
    checkedName := "v14ToyInterfaceBattery.test6_no_opaque_run_atom"
    note := "RawEvidence has no observer-output constructor and observers expand through observerToEvidence."
  },
  {
    item := "test 7 neutral skeleton not sufficient"
    status := .provedFromConstructedStructuralInterface
    checkedName := "v14ToyInterfaceBattery.test7_neutral_skeleton_not_target_sufficient"
    note := "Derived from the constructed no-public-target-tags field."
  },
  {
    item := "test 8 full public read decomposition"
    status := .constructionProved
    checkedName := "v14ToyInterfaceBattery_test8"
    note := "Neutral-only public reads are target-blind; safe-buffer and quotient reads have charged leaves."
  }
]

theorem v14ToyConstructionLedger_length :
    v14ToyConstructionLedger.length = 17 := by
  rfl

theorem v14ToyConstructionLedger_structural_fields_proved :
    (v14ToyConstructionLedger.get ⟨0, by decide⟩).status =
        V14ConstructionLedgerStatus.constructionProved ∧
      (v14ToyConstructionLedger.get ⟨1, by decide⟩).status =
        V14ConstructionLedgerStatus.constructionProved ∧
      (v14ToyConstructionLedger.get ⟨2, by decide⟩).status =
        V14ConstructionLedgerStatus.constructionProved ∧
      (v14ToyConstructionLedger.get ⟨3, by decide⟩).status =
        V14ConstructionLedgerStatus.constructionProved ∧
      (v14ToyConstructionLedger.get ⟨4, by decide⟩).status =
        V14ConstructionLedgerStatus.constructionProved ∧
      (v14ToyConstructionLedger.get ⟨8, by decide⟩).status =
        V14ConstructionLedgerStatus.constructionProved := by
  simp [v14ToyConstructionLedger]

theorem v14ToyConstructionLedger_analytic_frontier_carried :
    (v14ToyConstructionLedger.get ⟨5, by decide⟩).status =
        V14ConstructionLedgerStatus.carriedAnalyticFrontier ∧
      (v14ToyConstructionLedger.get ⟨6, by decide⟩).status =
        V14ConstructionLedgerStatus.carriedAnalyticFrontier ∧
      (v14ToyConstructionLedger.get ⟨7, by decide⟩).status =
        V14ConstructionLedgerStatus.carriedAnalyticFrontier := by
  simp [v14ToyConstructionLedger]

theorem v14ToyConstructionLedger_test8_proved :
    (v14ToyConstructionLedger.get ⟨16, by decide⟩).status =
      V14ConstructionLedgerStatus.constructionProved := by
  rfl

end Mettapedia.Computability.PNP
