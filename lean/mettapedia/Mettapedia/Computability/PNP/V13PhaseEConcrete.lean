import Mettapedia.Computability.PNP.V13FaithfulnessAudit

/-!
# PNP v13 Phase E: small locked SAT smoke instance

This module enters Phase E with a finite one-variable locked CNF family.  A
world contains a witness bit and a hidden gauge bit.  The public instance
contains the locked unit CNF and the Valiant-Vazirani-style row `x = rhs`;
the neutral skeleton hides `rhs`.  Each ledger obligation is discharged as a
separate lemma, with the expected safe-QSSM and boundary-mixing checks last.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-! ## One-variable locked CNF with a VV-style isolation row -/

inductive PhaseELit where
  | pos
  | neg
deriving DecidableEq, Repr

def PhaseELit.eval : PhaseELit -> Bool -> Bool
  | .pos, x => x
  | .neg, x => !x

abbrev PhaseEClause := List PhaseELit
abbrev PhaseECNF := List PhaseEClause

def PhaseEClause.eval (C : PhaseEClause) (x : Bool) : Bool :=
  C.any (fun lit => lit.eval x)

def PhaseECNF.eval (F : PhaseECNF) (x : Bool) : Bool :=
  F.all (fun C => C.eval x)

def phaseELockedCNF (rhs : Bool) : PhaseECNF :=
  if rhs then [[.pos]] else [[.neg]]

def phaseEVVAccept (rhs witness : Bool) : Bool :=
  witness == rhs

theorem phaseELockedCNF_sat_iff (rhs witness : Bool) :
    (phaseELockedCNF rhs).eval witness = true ↔ witness = rhs := by
  cases rhs <;> cases witness <;>
    simp [phaseELockedCNF, PhaseECNF.eval, PhaseEClause.eval,
      PhaseELit.eval]

theorem phaseEVVAccept_iff (rhs witness : Bool) :
    phaseEVVAccept rhs witness = true ↔ witness = rhs := by
  cases rhs <;> cases witness <;> simp [phaseEVVAccept]

theorem phaseELockedCNF_unique (rhs witness₀ witness₁ : Bool)
    (h₀ : (phaseELockedCNF rhs).eval witness₀ = true)
    (h₁ : (phaseELockedCNF rhs).eval witness₁ = true) :
    witness₀ = witness₁ := by
  exact
    (phaseELockedCNF_sat_iff rhs witness₀).mp h₀ |>.trans
      ((phaseELockedCNF_sat_iff rhs witness₁).mp h₁).symm

/-! ## Concrete finite worlds and public surface -/

abbrev PhaseEWorld := Bool × Bool

def PhaseEWorld.witness (omega : PhaseEWorld) : Bool :=
  omega.1

def PhaseEWorld.gauge (omega : PhaseEWorld) : Bool :=
  omega.2

structure PhaseEPublic where
  rhs : Bool
deriving DecidableEq, Repr

def phaseEPublicInput (omega : PhaseEWorld) : PhaseEPublic where
  rhs := omega.witness

def phaseENeutralSkeleton (_omega : PhaseEWorld) : Unit :=
  ()

def phaseETarget (omega : PhaseEWorld) : Bool :=
  omega.witness

def phaseETranscript (omega : PhaseEWorld) : Bool :=
  omega.witness

def phaseEObserverBit (t : Bool) : Bool :=
  t

def phaseEOppositeSupport (w0 w1 : PhaseEWorld) : Prop :=
  phaseETarget w0 = false ∧ phaseETarget w1 = true

def phaseETargetTrueEquiv :
    {omega : PhaseEWorld // phaseETarget omega = true} ≃ Bool where
  toFun omega := omega.val.2
  invFun g := ⟨(true, g), rfl⟩
  left_inv := by
    intro omega
    rcases omega with ⟨⟨w, g⟩, hw⟩
    cases w <;> simp [phaseETarget, PhaseEWorld.witness] at hw ⊢
  right_inv := by
    intro g
    rfl

def phaseETargetFalseEquiv :
    {omega : PhaseEWorld // phaseETarget omega = false} ≃ Bool where
  toFun omega := omega.val.2
  invFun g := ⟨(false, g), rfl⟩
  left_inv := by
    intro omega
    rcases omega with ⟨⟨w, g⟩, hw⟩
    cases w <;> simp [phaseETarget, PhaseEWorld.witness] at hw ⊢
  right_inv := by
    intro g
    rfl

theorem phaseE_card_target_true :
    Fintype.card {omega : PhaseEWorld // phaseETarget omega = true} = 2 := by
  rw [Fintype.card_congr phaseETargetTrueEquiv]
  norm_num

theorem phaseE_card_target_false :
    Fintype.card {omega : PhaseEWorld // phaseETarget omega = false} = 2 := by
  rw [Fintype.card_congr phaseETargetFalseEquiv]
  norm_num

def phaseEPredictTrueCorrectEquiv :
    {omega : PhaseEWorld //
      (fun _ : PhaseEWorld => true) omega = phaseETarget omega} ≃ Bool where
  toFun omega := omega.val.2
  invFun g := ⟨(true, g), rfl⟩
  left_inv := by
    intro omega
    rcases omega with ⟨⟨w, g⟩, hw⟩
    cases w <;> simp [phaseETarget, PhaseEWorld.witness] at hw ⊢
  right_inv := by
    intro g
    rfl

theorem phaseE_card_predict_true_correct :
    Fintype.card
      {omega : PhaseEWorld //
        (fun _ : PhaseEWorld => true) omega = phaseETarget omega} = 2 := by
  rw [Fintype.card_congr phaseEPredictTrueCorrectEquiv]
  norm_num

theorem phaseE_public_instance_is_locked (omega : PhaseEWorld) :
    (phaseELockedCNF (phaseEPublicInput omega).rhs).eval omega.witness = true ∧
      phaseEVVAccept (phaseEPublicInput omega).rhs omega.witness = true := by
  constructor
  · exact (phaseELockedCNF_sat_iff omega.witness omega.witness).mpr rfl
  · exact (phaseEVVAccept_iff omega.witness omega.witness).mpr rfl

/-! ## Phase A spine for the concrete family -/

def phaseELaw : FiniteRationalLaw PhaseEWorld where
  weight := fun _ => (1 / 4 : Rat)
  nonnegative := by
    intro omega
    norm_num
  total_weight := by
    norm_num

theorem phaseE_eventWeight_target_true :
    phaseELaw.eventWeight (fun omega => phaseETarget omega = true) =
      (1 / 2 : Rat) := by
  unfold FiniteRationalLaw.eventWeight phaseELaw phaseETarget
  rw [← Finset.univ_product_univ, Finset.sum_product]
  norm_num [PhaseEWorld.witness]

theorem phaseE_eventWeight_target_false :
    phaseELaw.eventWeight (fun omega => phaseETarget omega = false) =
      (1 / 2 : Rat) := by
  unfold FiniteRationalLaw.eventWeight phaseELaw phaseETarget
  rw [← Finset.univ_product_univ, Finset.sum_product]
  norm_num [PhaseEWorld.witness]

theorem phaseE_eventWeight_true_and_observer_true :
    phaseELaw.eventWeight
        (fun omega =>
          phaseETarget omega = true ∧
            phaseEObserverBit (phaseETranscript omega) = true) =
      (1 / 2 : Rat) := by
  unfold FiniteRationalLaw.eventWeight phaseELaw phaseETarget
    phaseETranscript phaseEObserverBit
  rw [← Finset.univ_product_univ, Finset.sum_product]
  norm_num [PhaseEWorld.witness]

theorem phaseE_eventWeight_false_and_observer_true :
    phaseELaw.eventWeight
        (fun omega =>
          phaseETarget omega = false ∧
            phaseEObserverBit (phaseETranscript omega) = true) =
      (0 : Rat) := by
  unfold FiniteRationalLaw.eventWeight phaseELaw phaseETarget
    phaseETranscript phaseEObserverBit
  rw [← Finset.univ_product_univ, Finset.sum_product]
  norm_num [PhaseEWorld.witness]

theorem phaseE_gap_eq_half :
    Gap phaseELaw phaseETarget phaseETranscript phaseEObserverBit =
      (1 / 2 : Rat) := by
  unfold Gap halfAbsDiff FiniteRationalLaw.conditionalProb
  rw [phaseE_eventWeight_true_and_observer_true,
    phaseE_eventWeight_target_true,
    phaseE_eventWeight_false_and_observer_true,
    phaseE_eventWeight_target_false]
  norm_num

def phaseEStaticCapture :
    StaticPairwiseCapture phaseELaw phaseETarget
      phaseETranscript phaseEObserverBit Bool where
  pairWeight := fun _ => (1 / 2 : Rat)
  pairNonnegative := by
    intro p
    norm_num
  left := fun g => (false, g)
  right := fun g => (true, g)
  opposite := by
    intro p
    exact ⟨rfl, rfl⟩

theorem phaseEStaticCapture_sepMass :
    phaseEStaticCapture.sepMass = 1 := by
  norm_num [StaticPairwiseCapture.sepMass, couplingSepMass,
    phaseEStaticCapture, phaseETranscript, PhaseEWorld.witness]

theorem phaseEStaticCapture_capturesGap :
    phaseEStaticCapture.CapturesGap := by
  rw [StaticPairwiseCapture.CapturesGap, phaseE_gap_eq_half,
    phaseEStaticCapture_sepMass]
  norm_num

def phaseETelescoping :
    DerivativeTelescoping Unit Unit where
  stageFinite := inferInstance
  branchFinite := inferInstance
  finalWeight := 0
  derivative := fun _ _ => 1
  derivativeNonnegative := by
    intro r h
    norm_num
  telescopes := by
    norm_num

def phaseEEvidenceSpineBound :
    EvidenceSpineBound phaseELaw phaseETarget
      phaseETranscript phaseEObserverBit Bool Unit Unit where
  capture := phaseEStaticCapture
  capturesGap := phaseEStaticCapture_capturesGap
  telescoping := phaseETelescoping
  sep_le_derivativeSum := by
    rw [phaseEStaticCapture_sepMass]
    unfold DerivativeTelescoping.derivativeSum
    norm_num [phaseETelescoping]

/-! ## Phase B evidence surface for the concrete family -/

def PhaseENeutral := Unit

inductive PhaseESafe where
  | cnfRead
  | vvRead
deriving DecidableEq, Repr

def PhaseEGauge := Unit

def phaseESemantics :
    EvidenceSemantics PhaseEWorld PhaseENeutral PhaseESafe PhaseEGauge where
  neutralSat := fun _ _ => True
  safeSat := fun _ _ => True
  gaugeSat := fun _ _ => True

def phaseEObserverEvidenceInterface :
    ObserverEvidenceInterface
      PhaseEWorld PhaseEPublic Unit Unit PhaseENeutral PhaseESafe PhaseEGauge where
  semantics := phaseESemantics
  publicInput := phaseEPublicInput
  evalObserver := fun _ _ => ()
  observerToEvidence := fun _ _ => .top
  observerToEvidence_sat := by
    intro observer output
    funext omega
    cases output
    simp [EvidenceSemantics.SatRaw]

/-! ## Concrete history and pivot surfaces -/

def phaseEHistoryField : FiniteSigmaField PhaseEWorld where
  Atom := Unit
  atomDecidable := inferInstance
  atom := fun _ => ()

def phaseEPivot (_omega : PhaseEWorld) : Unit :=
  ()

theorem phaseE_balanced_target :
    BalancedBit phaseETarget := by
  unfold BalancedBit globalDecoderSuccess
  have hcard :
      Fintype.card
        {phi : PhaseEWorld // (fun _ : PhaseEWorld => true) phi =
          phaseETarget phi} = 2 := by
    exact phaseE_card_predict_true_correct
  rw [hcard]
  norm_num

theorem phaseE_balanced_conditioning :
    BalancedConditioning phaseEHistoryField phaseETarget := by
  intro a
  cases a
  simpa [phaseEHistoryField, FiberTrue, FiberFalse] using
    phaseE_card_target_true.trans phaseE_card_target_false.symm

theorem phaseE_boundary_mixing_zero :
    BoundaryMixingBound phaseETarget phaseEPivot 0 := by
  intro h
  cases hval : h ()
  · have hcard :
        Fintype.card
          {phi : PhaseEWorld // (fun w => h (phaseEPivot w)) phi =
            phaseETarget phi} = 2 := by
        simpa [phaseEPivot, hval] using phaseE_card_target_false
    have hsuccess :
        globalDecoderSuccess (fun w => h (phaseEPivot w))
          phaseETarget = (1 / 2 : Rat) := by
      unfold globalDecoderSuccess
      rw [hcard]
      norm_num
    rw [hsuccess, phaseE_balanced_target]
    norm_num
  · have hcard :
        Fintype.card
          {phi : PhaseEWorld // (fun w => h (phaseEPivot w)) phi =
            phaseETarget phi} = 2 := by
        simpa [phaseEPivot, hval] using phaseE_card_target_true
    have hsuccess :
        globalDecoderSuccess (fun w => h (phaseEPivot w))
          phaseETarget = (1 / 2 : Rat) := by
      unfold globalDecoderSuccess
      rw [hcard]
      norm_num
    rw [hsuccess, phaseE_balanced_target]
    norm_num

/-! ## The nine Phase E obligations, discharged one by one -/

theorem phaseE_singleMessage :
    ∀ w0 w1, phaseEPublicInput w0 = phaseEPublicInput w1 ->
      phaseETarget w0 = phaseETarget w1 := by
  intro w0 w1 h
  exact congrArg PhaseEPublic.rhs h

theorem phaseE_noPublicTargetTags :
    PairNeutral phaseEOppositeSupport phaseENeutralSkeleton ∧
      HasMessageOppositePair phaseEOppositeSupport phaseETarget ∧
        ¬ ∃ f : Unit -> Bool,
          ∀ omega, phaseETarget omega = f (phaseENeutralSkeleton omega) := by
  refine ⟨?neutral, ?opp, ?notSuff⟩
  · intro w0 w1 h
    rfl
  · exact ⟨(false, false), (true, false), ⟨rfl, rfl⟩, rfl, rfl⟩
  · intro h
    rcases h with ⟨f, hf⟩
    have hfalse := hf (false, false)
    have htrue := hf (true, false)
    rw [phaseETarget, PhaseEWorld.witness] at hfalse htrue
    rw [← hfalse] at htrue
    cases htrue

theorem phaseE_atomCompleteness :
    ∀ E : RawEvidence PhaseENeutral PhaseESafe PhaseEGauge,
      phaseESemantics.SatNormal (CDENF E) =
        phaseESemantics.SatRaw E := by
  intro E
  exact CDENF_semantics phaseESemantics E

theorem phaseE_gaugeFaithfulness :
    ∀ gamma : PhaseEGauge,
      phaseESemantics.SatNormal (CDENF (.gauge gamma)) =
        phaseESemantics.gaugeSat gamma := by
  intro gamma
  cases gamma
  rfl

theorem phaseE_gaugePredicateTotal :
    ∀ gamma omega, phaseESemantics.gaugeSat gamma omega := by
  intro gamma omega
  cases gamma
  trivial

def phaseEGaugeIncidence (_gamma : PhaseEGauge) : Nat :=
  1

theorem phaseE_boundedGaugeIncidence :
    ∀ gamma : PhaseEGauge, phaseEGaugeIncidence gamma ≤ 1 := by
  intro gamma
  cases gamma
  norm_num [phaseEGaugeIncidence]

theorem phaseE_admissibleHistories :
    BalancedBit phaseETarget ∧
      BalancedConditioning phaseEHistoryField phaseETarget :=
  ⟨phaseE_balanced_target, phaseE_balanced_conditioning⟩

def phaseESafeCost (_q : PhaseESafe) : Rat :=
  0

theorem phaseE_safeQSSM :
    ∀ q : PhaseESafe, 0 ≤ phaseESafeCost q ∧ phaseESafeCost q ≤ 0 := by
  intro q
  cases q <;> norm_num [phaseESafeCost]

theorem phaseE_boundaryMixing :
    BoundaryMixingBound phaseETarget phaseEPivot 0 :=
  phaseE_boundary_mixing_zero

def phaseELockedInterface :
    GaugeBufferedLockedInterface
      PhaseEWorld PhaseEPublic PhaseENeutral PhaseESafe PhaseEGauge Bool Bool
      Unit Unit Unit Unit Unit Unit Unit where
  law := phaseELaw
  target := phaseETarget
  publicInput := phaseEPublicInput
  neutralSkeleton := phaseENeutralSkeleton
  oppositeSupport := phaseEOppositeSupport
  transcript := phaseETranscript
  observerBit := phaseEObserverBit
  phaseA := phaseEEvidenceSpineBound
  semantics := phaseESemantics
  observerEvidence := phaseEObserverEvidenceInterface
  historyField := phaseEHistoryField
  pivotSummary := phaseEPivot
  epsMix := 0
  safeCost := phaseESafeCost
  safeBudget := 0
  gaugeIncidence := phaseEGaugeIncidence
  gaugeBound := 1
  singleMessage := phaseE_singleMessage
  gaugePredicateTotal := phaseE_gaugePredicateTotal
  noPublicTargetTags := phaseE_noPublicTargetTags
  atomCompleteness := phaseE_atomCompleteness
  gaugeFaithfulness := phaseE_gaugeFaithfulness
  safeQSSM := phaseE_safeQSSM
  boundedGaugeIncidence := phaseE_boundedGaugeIncidence
  boundaryMixing := phaseE_boundaryMixing
  admissibleHistories := phaseE_admissibleHistories

/-! ## Phase E obligation map -/

inductive PhaseEObligationStatus where
  | discharged
  | openForScaledFamily
  | failed
deriving DecidableEq, Repr

structure PhaseEObligationRow where
  fieldName : String
  status : PhaseEObligationStatus
  finding : String
deriving Repr

def phaseEObligationMap : List PhaseEObligationRow := [
  {
    fieldName := "singleMessage"
    status := .discharged
    finding := "Public RHS fixes the unique satisfying witness bit in the locked unit CNF."
  },
  {
    fieldName := "noPublicTargetTags"
    status := .discharged
    finding := "Neutral skeleton is Unit, so it is pair-neutral but cannot determine the target."
  },
  {
    fieldName := "atomCompleteness"
    status := .discharged
    finding := "Inherited from CDENF semantic preservation for all raw evidence."
  },
  {
    fieldName := "gaugeFaithfulness"
    status := .discharged
    finding := "The one hidden gauge coordinate has no canonical public shortcut in this smoke instance."
  },
  {
    fieldName := "gaugePredicateTotal"
    status := .discharged
    finding := "Gauge evidence is hidden and universally satisfied in the abstract evidence semantics."
  },
  {
    fieldName := "boundedGaugeIncidence"
    status := .discharged
    finding := "The single gauge coordinate has incidence one."
  },
  {
    fieldName := "admissibleHistories"
    status := .discharged
    finding := "The Unit history field leaves two worlds in each target phase."
  },
  {
    fieldName := "safeQSSM"
    status := .discharged
    finding := "Safe costs are zero in this finite smoke instance; scaled max-qSSM remains a separate obligation."
  },
  {
    fieldName := "boundaryMixing"
    status := .discharged
    finding := "The Unit pivot summary has exact half success; scaled boundary-law mixing remains a separate obligation."
  }
]

theorem phaseEObligationMap_length :
    phaseEObligationMap.length = 9 := by
  rfl

theorem phaseEObligationMap_has_no_failures :
    ∀ row ∈ phaseEObligationMap, row.status ≠ .failed := by
  intro row hmem
  simp [phaseEObligationMap] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  all_goals subst row; decide

def PhaseEAllNineObligations : Prop :=
    (∀ w0 w1, phaseEPublicInput w0 = phaseEPublicInput w1 ->
      phaseETarget w0 = phaseETarget w1) ∧
      (PairNeutral phaseEOppositeSupport phaseENeutralSkeleton ∧
        HasMessageOppositePair phaseEOppositeSupport phaseETarget ∧
          ¬ ∃ f : Unit -> Bool,
            ∀ omega, phaseETarget omega = f (phaseENeutralSkeleton omega)) ∧
      (∀ E : RawEvidence PhaseENeutral PhaseESafe PhaseEGauge,
        phaseESemantics.SatNormal (CDENF E) =
          phaseESemantics.SatRaw E) ∧
      (∀ gamma : PhaseEGauge,
        phaseESemantics.SatNormal (CDENF (.gauge gamma)) =
          phaseESemantics.gaugeSat gamma) ∧
      (∀ gamma omega, phaseESemantics.gaugeSat gamma omega) ∧
      (∀ gamma : PhaseEGauge, phaseEGaugeIncidence gamma ≤ 1) ∧
      (BalancedBit phaseETarget ∧
        BalancedConditioning phaseEHistoryField phaseETarget) ∧
      (∀ q : PhaseESafe, 0 ≤ phaseESafeCost q ∧ phaseESafeCost q ≤ 0) ∧
      BoundaryMixingBound phaseETarget phaseEPivot 0

theorem phaseE_all_nine_obligations :
    PhaseEAllNineObligations := by
  exact
    ⟨phaseE_singleMessage,
      phaseE_noPublicTargetTags,
      phaseE_atomCompleteness,
      phaseE_gaugeFaithfulness,
      phaseE_gaugePredicateTotal,
      phaseE_boundedGaugeIncidence,
      phaseE_admissibleHistories,
      phaseE_safeQSSM,
      phaseE_boundaryMixing⟩

end Mettapedia.Computability.PNP
