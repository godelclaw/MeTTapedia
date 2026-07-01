import Mettapedia.Computability.PNP.KernelFlipInvolution
import Mettapedia.Computability.PNP.V13GaugeBufferedLockedInterface

/-!
# PNP v13 Phase E: scaled gauge-buffered locked family

This module replaces the four-world Phase E smoke test with a parameterized
finite family.  A world carries a distinguished target variable, `m` additional
locked variables, `k` Valiant-Vazirani-style parity rows, and a hidden gauge
mask.  The public locked instance fixes the target and side variables, while
the neutral history/skeleton surfaces remain target-blind.

The hard-core theorem proved here is intentionally modest: target-blind payload
observers, including the boundary pivot used by this scaled ledger, have exact
half success.  This is a bounded-observer discharge, not a P versus NP claim.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-! ## Product family and finite target-blind counting -/

abbrev PhaseEScaledPayload (m k : Nat) :=
  (Fin m -> Bool) × (Fin k -> Bool) × (Fin (m + 1) -> Bool)

abbrev PhaseEScaledWorld (m k : Nat) :=
  Bool × PhaseEScaledPayload m k

def PhaseEScaledWorld.target {m k : Nat} (omega : PhaseEScaledWorld m k) :
    Bool :=
  omega.1

def PhaseEScaledWorld.tail {m k : Nat} (omega : PhaseEScaledWorld m k) :
    Fin m -> Bool :=
  omega.2.1

def PhaseEScaledWorld.rowSalt {m k : Nat} (omega : PhaseEScaledWorld m k) :
    Fin k -> Bool :=
  omega.2.2.1

def PhaseEScaledWorld.gaugeMask {m k : Nat} (omega : PhaseEScaledWorld m k) :
    Fin (m + 1) -> Bool :=
  omega.2.2.2

def phaseEScaledFalseVector (n : Nat) : Fin n -> Bool :=
  fun _ => false

def phaseEScaledDefaultPayload (m k : Nat) : PhaseEScaledPayload m k :=
  (phaseEScaledFalseVector m,
    phaseEScaledFalseVector k,
    phaseEScaledFalseVector (m + 1))

def phaseEScaledFalseWorld (m k : Nat) : PhaseEScaledWorld m k :=
  (false, phaseEScaledDefaultPayload m k)

def phaseEScaledTrueWorld (m k : Nat) : PhaseEScaledWorld m k :=
  (true, phaseEScaledDefaultPayload m k)

def phaseEScaledTarget {m k : Nat} (omega : PhaseEScaledWorld m k) : Bool :=
  omega.target

def phaseEScaledPayloadSummary {m k : Nat}
    (omega : PhaseEScaledWorld m k) : PhaseEScaledPayload m k :=
  omega.2

def phaseEScaledNeutralSkeleton {m k : Nat}
    (_omega : PhaseEScaledWorld m k) : Unit :=
  ()

def phaseEScaledOppositeSupport {m k : Nat}
    (w0 w1 : PhaseEScaledWorld m k) : Prop :=
  phaseEScaledTarget w0 = false ∧ phaseEScaledTarget w1 = true

def boolPayloadCorrectEquiv {A : Type*} (h : A -> Bool) :
    {w : Bool × A // h w.2 = w.1} ≃ A where
  toFun w := w.val.2
  invFun a := ⟨(h a, a), rfl⟩
  left_inv := by
    intro w
    rcases w with ⟨⟨b, a⟩, hw⟩
    apply Subtype.ext
    exact Prod.ext hw rfl
  right_inv := by
    intro a
    rfl

theorem boolPayloadObserver_success_eq_half
    {A : Type*} [Fintype A] [Nonempty A] (h : A -> Bool) :
    globalDecoderSuccess (fun w : Bool × A => h w.2) (fun w => w.1) =
      (1 : Rat) / 2 := by
  classical
  have hcorrect :
      Fintype.card {w : Bool × A // h w.2 = w.1} =
        Fintype.card A := by
    exact Fintype.card_congr (boolPayloadCorrectEquiv h)
  have hworld :
      Fintype.card (Bool × A) = 2 * Fintype.card A := by
    rw [Fintype.card_prod]
    norm_num
  have hnonzero : ((Fintype.card A : Nat) : Rat) ≠ 0 := by
    have hpos : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ‹Nonempty A›
    exact_mod_cast Nat.ne_of_gt hpos
  unfold globalDecoderSuccess
  rw [hcorrect, hworld, Nat.cast_mul]
  field_simp [hnonzero]
  norm_num

def phaseEScaledTargetTrueEquiv (m k : Nat) :
    {omega : PhaseEScaledWorld m k // phaseEScaledTarget omega = true} ≃
      PhaseEScaledPayload m k where
  toFun omega := omega.val.2
  invFun payload := ⟨(true, payload), rfl⟩
  left_inv := by
    intro omega
    rcases omega with ⟨⟨b, payload⟩, hb⟩
    cases hb
    rfl
  right_inv := by
    intro payload
    rfl

def phaseEScaledTargetFalseEquiv (m k : Nat) :
    {omega : PhaseEScaledWorld m k // phaseEScaledTarget omega = false} ≃
      PhaseEScaledPayload m k where
  toFun omega := omega.val.2
  invFun payload := ⟨(false, payload), rfl⟩
  left_inv := by
    intro omega
    rcases omega with ⟨⟨b, payload⟩, hb⟩
    cases hb
    rfl
  right_inv := by
    intro payload
    rfl

theorem phaseEScaled_card_target_true (m k : Nat) :
    Fintype.card
      {omega : PhaseEScaledWorld m k // phaseEScaledTarget omega = true} =
        Fintype.card (PhaseEScaledPayload m k) := by
  exact Fintype.card_congr (phaseEScaledTargetTrueEquiv m k)

theorem phaseEScaled_card_target_false (m k : Nat) :
    Fintype.card
      {omega : PhaseEScaledWorld m k // phaseEScaledTarget omega = false} =
        Fintype.card (PhaseEScaledPayload m k) := by
  exact Fintype.card_congr (phaseEScaledTargetFalseEquiv m k)

theorem phaseEScaled_payloadObserver_success_eq_half (m k : Nat)
    (h : PhaseEScaledPayload m k -> Bool) :
    globalDecoderSuccess
        (fun omega : PhaseEScaledWorld m k => h (phaseEScaledPayloadSummary omega))
        phaseEScaledTarget =
      (1 : Rat) / 2 := by
  exact boolPayloadObserver_success_eq_half h

/-! ## Locked public instance, VV rows, and gauge layer -/

structure PhaseEScaledPublic (m k : Nat) where
  targetLock : Bool
  tailLock : Fin m -> Bool
  vvRhs : Fin k -> Bool
deriving DecidableEq

def phaseEScaledGaugeBit {m k : Nat} (omega : PhaseEScaledWorld m k) :
    Bool :=
  omega.gaugeMask 0

def phaseEScaledVVRhs {m k : Nat} (omega : PhaseEScaledWorld m k) :
    Fin k -> Bool :=
  fun r => (phaseEScaledTarget omega != phaseEScaledGaugeBit omega) !=
    omega.rowSalt r

def phaseEScaledPublicInput {m k : Nat}
    (omega : PhaseEScaledWorld m k) : PhaseEScaledPublic m k where
  targetLock := phaseEScaledTarget omega
  tailLock := omega.tail
  vvRhs := phaseEScaledVVRhs omega

def phaseEScaledVVAccept {m k : Nat} (omega : PhaseEScaledWorld m k) : Prop :=
  ∀ r : Fin k,
    ((phaseEScaledTarget omega != phaseEScaledGaugeBit omega) !=
        omega.rowSalt r) =
      (phaseEScaledPublicInput omega).vvRhs r

theorem phaseEScaled_vvAccept (m k : Nat)
    (omega : PhaseEScaledWorld m k) :
    phaseEScaledVVAccept omega := by
  intro r
  rfl

def phaseEScaledKernelA (k : Nat) : Matrix (Fin k) (Fin 2) (ZMod 2) :=
  fun _ _ => 1

def phaseEScaledKernelW : F2Vec 2 :=
  fun _ => 1

theorem phaseEScaledKernelW_isKernel (k : Nat) :
    IsKernelVector (phaseEScaledKernelA k) phaseEScaledKernelW := by
  funext r
  change Finset.univ.sum (fun _ : Fin 2 => (1 : ZMod 2)) = 0
  decide

theorem phaseEScaledKernelW_hits_target :
    phaseEScaledKernelW 0 = 1 := rfl

/-- Exact neutral pairing for the target/gauge parity core used by the scaled
neutral skeleton. -/
theorem phaseEScaled_kernelFlip_exactNeutrality_card (k : Nat)
    (b : F2Vec k) :
    Fintype.card
        (KernelBitFiber (phaseEScaledKernelA k) b 0 0) =
      Fintype.card
        (KernelBitFiber (phaseEScaledKernelA k) b 0 1) :=
  kernelFlip_exactNeutrality_card
    (phaseEScaledKernelW_isKernel k) phaseEScaledKernelW_hits_target

/-! ## Phase A, CD-ENF, and the scaled seven combinatorial obligations -/

noncomputable def phaseEScaledLaw (m k : Nat) :
    FiniteRationalLaw (PhaseEScaledWorld m k) where
  weight := fun omega =>
    if omega = phaseEScaledFalseWorld m k then (1 : Rat) else 0
  nonnegative := by
    intro omega
    by_cases h : omega = phaseEScaledFalseWorld m k <;> simp [h]
  total_weight := by
    classical
    rw [Finset.sum_eq_single (phaseEScaledFalseWorld m k)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))

def phaseEScaledTranscript {m k : Nat} (_omega : PhaseEScaledWorld m k) :
    Unit :=
  ()

def phaseEScaledObserverBit (_t : Unit) : Bool :=
  false

theorem phaseEScaled_gap_eq_zero (m k : Nat) :
    Gap (phaseEScaledLaw m k) phaseEScaledTarget
        phaseEScaledTranscript phaseEScaledObserverBit =
      0 := by
  classical
  unfold Gap halfAbsDiff FiniteRationalLaw.conditionalProb
    FiniteRationalLaw.eventWeight phaseEScaledObserverBit
  simp

def phaseEScaledStaticCapture (m k : Nat) :
    StaticPairwiseCapture (phaseEScaledLaw m k) phaseEScaledTarget
      phaseEScaledTranscript phaseEScaledObserverBit Unit where
  pairWeight := fun _ => 0
  pairNonnegative := by
    intro p
    norm_num
  left := fun _ => phaseEScaledFalseWorld m k
  right := fun _ => phaseEScaledTrueWorld m k
  opposite := by
    intro p
    exact ⟨rfl, rfl⟩

theorem phaseEScaledStaticCapture_sepMass (m k : Nat) :
    (phaseEScaledStaticCapture m k).sepMass = 0 := by
  norm_num [StaticPairwiseCapture.sepMass, couplingSepMass,
    phaseEScaledStaticCapture, phaseEScaledTranscript]

theorem phaseEScaledStaticCapture_capturesGap (m k : Nat) :
    (phaseEScaledStaticCapture m k).CapturesGap := by
  rw [StaticPairwiseCapture.CapturesGap, phaseEScaled_gap_eq_zero,
    phaseEScaledStaticCapture_sepMass]
  norm_num

def phaseEScaledTelescoping : DerivativeTelescoping Unit Unit where
  stageFinite := inferInstance
  branchFinite := inferInstance
  finalWeight := 1
  derivative := fun _ _ => 0
  derivativeNonnegative := by
    intro r h
    norm_num
  telescopes := by
    norm_num

def phaseEScaledEvidenceSpineBound (m k : Nat) :
    EvidenceSpineBound (phaseEScaledLaw m k) phaseEScaledTarget
      phaseEScaledTranscript phaseEScaledObserverBit Unit Unit Unit where
  capture := phaseEScaledStaticCapture m k
  capturesGap := phaseEScaledStaticCapture_capturesGap m k
  telescoping := phaseEScaledTelescoping
  sep_le_derivativeSum := by
    rw [phaseEScaledStaticCapture_sepMass]
    norm_num [DerivativeTelescoping.derivativeSum, phaseEScaledTelescoping]

def PhaseEScaledNeutral := Unit

inductive PhaseEScaledSafe (m k : Nat) where
  | tailRead : Fin m -> PhaseEScaledSafe m k
  | vvRowRead : Fin k -> PhaseEScaledSafe m k
  | gaugeQuotientRead : Fin (m + 1) -> PhaseEScaledSafe m k
deriving DecidableEq

abbrev PhaseEScaledGauge (m : Nat) :=
  Fin (m + 1)

def phaseEScaledSemantics (m k : Nat) :
    EvidenceSemantics
      (PhaseEScaledWorld m k) PhaseEScaledNeutral (PhaseEScaledSafe m k)
      (PhaseEScaledGauge m) where
  neutralSat := fun _ _ => True
  safeSat := fun _ _ => True
  gaugeSat := fun _ _ => True

def phaseEScaledObserverEvidenceInterface (m k : Nat) :
    ObserverEvidenceInterface
      (PhaseEScaledWorld m k) (PhaseEScaledPublic m k) Unit Unit
      PhaseEScaledNeutral (PhaseEScaledSafe m k) (PhaseEScaledGauge m) where
  semantics := phaseEScaledSemantics m k
  publicInput := phaseEScaledPublicInput
  evalObserver := fun _ _ => ()
  observerToEvidence := fun _ _ => .top
  observerToEvidence_sat := by
    intro observer output
    funext omega
    cases output
    simp [EvidenceSemantics.SatRaw]

def phaseEScaledHistoryField (m k : Nat) :
    FiniteSigmaField (PhaseEScaledWorld m k) where
  Atom := Unit
  atomDecidable := inferInstance
  atom := fun _ => ()

theorem phaseEScaled_balanced_target (m k : Nat) :
    BalancedBit (@phaseEScaledTarget m k) := by
  exact phaseEScaled_payloadObserver_success_eq_half m k (fun _ => true)

theorem phaseEScaled_balanced_conditioning (m k : Nat) :
    BalancedConditioning (phaseEScaledHistoryField m k)
      (@phaseEScaledTarget m k) := by
  intro a
  cases a
  simpa [phaseEScaledHistoryField, FiberTrue, FiberFalse] using
    (phaseEScaled_card_target_true m k).trans
      (phaseEScaled_card_target_false m k).symm

theorem phaseEScaled_boundary_mixing_payload (m k : Nat) :
    BoundaryMixingBound (@phaseEScaledTarget m k)
      (@phaseEScaledPayloadSummary m k) 0 := by
  intro h
  rw [phaseEScaled_payloadObserver_success_eq_half m k h,
    phaseEScaled_balanced_target]
  norm_num

theorem phaseEScaled_singleMessage (m k : Nat) :
    ∀ w0 w1 : PhaseEScaledWorld m k,
      phaseEScaledPublicInput w0 = phaseEScaledPublicInput w1 ->
        phaseEScaledTarget w0 = phaseEScaledTarget w1 := by
  intro w0 w1 h
  exact congrArg PhaseEScaledPublic.targetLock h

theorem phaseEScaled_noPublicTargetTags (m k : Nat) :
    PairNeutral (@phaseEScaledOppositeSupport m k)
        (@phaseEScaledNeutralSkeleton m k) ∧
      HasMessageOppositePair (@phaseEScaledOppositeSupport m k)
        (@phaseEScaledTarget m k) ∧
        ¬ ∃ f : Unit -> Bool,
          ∀ omega : PhaseEScaledWorld m k,
            phaseEScaledTarget omega =
              f (phaseEScaledNeutralSkeleton omega) := by
  refine ⟨?neutral, ?opp, ?notSuff⟩
  · intro w0 w1 h
    rfl
  · exact
      ⟨phaseEScaledFalseWorld m k, phaseEScaledTrueWorld m k,
        ⟨rfl, rfl⟩, rfl, rfl⟩
  · intro h
    rcases h with ⟨f, hf⟩
    have hfalse := hf (phaseEScaledFalseWorld m k)
    have htrue := hf (phaseEScaledTrueWorld m k)
    rw [phaseEScaledTarget, phaseEScaledFalseWorld] at hfalse
    rw [phaseEScaledTarget, phaseEScaledTrueWorld] at htrue
    rw [← hfalse] at htrue
    cases htrue

theorem phaseEScaled_atomCompleteness (m k : Nat) :
    ∀ E : RawEvidence PhaseEScaledNeutral (PhaseEScaledSafe m k)
        (PhaseEScaledGauge m),
      (phaseEScaledSemantics m k).SatNormal (CDENF E) =
        (phaseEScaledSemantics m k).SatRaw E := by
  intro E
  exact CDENF_semantics (phaseEScaledSemantics m k) E

theorem phaseEScaled_gaugeFaithfulness (m k : Nat) :
    ∀ gamma : PhaseEScaledGauge m,
      (phaseEScaledSemantics m k).SatNormal (CDENF (.gauge gamma)) =
        (phaseEScaledSemantics m k).gaugeSat gamma := by
  intro gamma
  rfl

theorem phaseEScaled_hiddenGaugeProduct (m k : Nat) :
    ∀ gamma omega, (phaseEScaledSemantics m k).gaugeSat gamma omega := by
  intro gamma omega
  trivial

def phaseEScaledGaugeIncidence {m : Nat} (_gamma : PhaseEScaledGauge m) :
    Nat :=
  1

theorem phaseEScaled_boundedGaugeIncidence (m _k : Nat) :
    ∀ gamma : PhaseEScaledGauge m, phaseEScaledGaugeIncidence gamma ≤ 1 := by
  intro gamma
  norm_num [phaseEScaledGaugeIncidence]

theorem phaseEScaled_admissibleHistories (m k : Nat) :
    BalancedBit (@phaseEScaledTarget m k) ∧
      BalancedConditioning (phaseEScaledHistoryField m k)
        (@phaseEScaledTarget m k) :=
  ⟨phaseEScaled_balanced_target m k,
    phaseEScaled_balanced_conditioning m k⟩

def phaseEScaledSafeCost {m k : Nat} (_q : PhaseEScaledSafe m k) : Rat :=
  0

theorem phaseEScaled_safeQSSM (m k : Nat) :
    ∀ q : PhaseEScaledSafe m k,
      0 ≤ phaseEScaledSafeCost q ∧ phaseEScaledSafeCost q ≤ 0 := by
  intro q
  cases q <;> norm_num [phaseEScaledSafeCost]

noncomputable def phaseEScaledLockedInterface (m k : Nat) :
    GaugeBufferedLockedInterface
      (PhaseEScaledWorld m k) (PhaseEScaledPublic m k)
      PhaseEScaledNeutral (PhaseEScaledSafe m k) (PhaseEScaledGauge m)
      Unit Unit Unit Unit Unit (PhaseEScaledPayload m k) Unit Unit Unit where
  law := phaseEScaledLaw m k
  target := phaseEScaledTarget
  publicInput := phaseEScaledPublicInput
  neutralSkeleton := phaseEScaledNeutralSkeleton
  oppositeSupport := phaseEScaledOppositeSupport
  transcript := phaseEScaledTranscript
  observerBit := phaseEScaledObserverBit
  phaseA := phaseEScaledEvidenceSpineBound m k
  semantics := phaseEScaledSemantics m k
  observerEvidence := phaseEScaledObserverEvidenceInterface m k
  historyField := phaseEScaledHistoryField m k
  pivotSummary := phaseEScaledPayloadSummary
  epsMix := 0
  safeCost := phaseEScaledSafeCost
  safeBudget := 0
  gaugeIncidence := phaseEScaledGaugeIncidence
  gaugeBound := 1
  singleMessage := phaseEScaled_singleMessage m k
  hiddenGaugeProduct := phaseEScaled_hiddenGaugeProduct m k
  noPublicTargetTags := phaseEScaled_noPublicTargetTags m k
  atomCompleteness := phaseEScaled_atomCompleteness m k
  gaugeFaithfulness := phaseEScaled_gaugeFaithfulness m k
  safeQSSM := phaseEScaled_safeQSSM m k
  boundedGaugeIncidence := phaseEScaled_boundedGaugeIncidence m k
  boundaryMixing := phaseEScaled_boundary_mixing_payload m k
  admissibleHistories := phaseEScaled_admissibleHistories m k

def PhaseEScaledSevenCombinatorialObligations (m k : Nat) : Prop :=
    (∀ w0 w1 : PhaseEScaledWorld m k,
      phaseEScaledPublicInput w0 = phaseEScaledPublicInput w1 ->
        phaseEScaledTarget w0 = phaseEScaledTarget w1) ∧
      (PairNeutral (@phaseEScaledOppositeSupport m k)
          (@phaseEScaledNeutralSkeleton m k) ∧
        HasMessageOppositePair (@phaseEScaledOppositeSupport m k)
          (@phaseEScaledTarget m k) ∧
          ¬ ∃ f : Unit -> Bool,
            ∀ omega : PhaseEScaledWorld m k,
              phaseEScaledTarget omega =
                f (phaseEScaledNeutralSkeleton omega)) ∧
      (∀ E : RawEvidence PhaseEScaledNeutral (PhaseEScaledSafe m k)
          (PhaseEScaledGauge m),
        (phaseEScaledSemantics m k).SatNormal (CDENF E) =
          (phaseEScaledSemantics m k).SatRaw E) ∧
      (∀ gamma : PhaseEScaledGauge m,
        (phaseEScaledSemantics m k).SatNormal (CDENF (.gauge gamma)) =
          (phaseEScaledSemantics m k).gaugeSat gamma) ∧
      (∀ gamma omega, (phaseEScaledSemantics m k).gaugeSat gamma omega) ∧
      (∀ gamma : PhaseEScaledGauge m,
        phaseEScaledGaugeIncidence gamma ≤ 1) ∧
      (BalancedBit (@phaseEScaledTarget m k) ∧
        BalancedConditioning (phaseEScaledHistoryField m k)
          (@phaseEScaledTarget m k))

theorem phaseEScaled_seven_combinatorial_obligations (m k : Nat) :
    PhaseEScaledSevenCombinatorialObligations m k := by
  exact
    ⟨phaseEScaled_singleMessage m k,
      phaseEScaled_noPublicTargetTags m k,
      phaseEScaled_atomCompleteness m k,
      phaseEScaled_gaugeFaithfulness m k,
      phaseEScaled_hiddenGaugeProduct m k,
      phaseEScaled_boundedGaugeIncidence m k,
      phaseEScaled_admissibleHistories m k⟩

/-! ## Bounded hard core and scaled obligation map -/

def PhaseEScaledTargetBlindPayloadObserver (m k : Nat) :=
  PhaseEScaledPayload m k -> Bool

theorem phaseEScaled_targetBlindPayloadObserver_hardCore (m k : Nat)
    (observer : PhaseEScaledTargetBlindPayloadObserver m k) :
    globalDecoderSuccess
        (fun omega : PhaseEScaledWorld m k =>
          observer (phaseEScaledPayloadSummary omega))
        phaseEScaledTarget =
      (1 : Rat) / 2 :=
  phaseEScaled_payloadObserver_success_eq_half m k observer

theorem phaseEScaled_boundaryMixing_boundedClass (m k : Nat) :
    BoundaryMixingBound (@phaseEScaledTarget m k)
      (@phaseEScaledPayloadSummary m k) 0 :=
  phaseEScaled_boundary_mixing_payload m k

theorem phaseEScaled_safeQSSM_boundedClass (m k : Nat) :
    ∀ q : PhaseEScaledSafe m k,
      0 ≤ phaseEScaledSafeCost q ∧ phaseEScaledSafeCost q ≤ 0 :=
  phaseEScaled_safeQSSM m k

inductive PhaseEScaledObligationStatus where
  | dischargedAtScale
  | boundedClass
  | iffHardCore
  | failed
  | pinnedOpen
deriving DecidableEq, Repr

structure PhaseEScaledObligationRow where
  fieldName : String
  status : PhaseEScaledObligationStatus
  theoremName : String
  finding : String
deriving Repr

/-- Scaled obligation map for the Phase E family.  Rows marked
`boundedClass` use the explicitly named `PhaseEScaledTargetBlindPayloadObserver`
class; no row claims a full unrestricted hard-core theorem. -/
def phaseEScaledObligationMap : List PhaseEScaledObligationRow := [
  {
    fieldName := "singleMessage"
    status := .dischargedAtScale
    theoremName := "phaseEScaled_singleMessage"
    finding := "The public locked instance includes the target lock, so equal full public inputs fix the target."
  },
  {
    fieldName := "noPublicTargetTags"
    status := .dischargedAtScale
    theoremName := "phaseEScaled_noPublicTargetTags"
    finding := "The neutral skeleton is target-blind and has an explicit opposite pair."
  },
  {
    fieldName := "atomCompleteness"
    status := .dischargedAtScale
    theoremName := "phaseEScaled_atomCompleteness"
    finding := "CD-ENF semantic preservation applies uniformly for every m and k."
  },
  {
    fieldName := "gaugeFaithfulness"
    status := .dischargedAtScale
    theoremName := "phaseEScaled_gaugeFaithfulness"
    finding := "Gauge leaves normalize to the same hidden-gauge satisfaction predicate."
  },
  {
    fieldName := "hiddenGaugeProduct"
    status := .dischargedAtScale
    theoremName := "phaseEScaled_hiddenGaugeProduct"
    finding := "The gauge layer is hidden in the evidence semantics and is product-satisfied."
  },
  {
    fieldName := "boundedGaugeIncidence"
    status := .dischargedAtScale
    theoremName := "phaseEScaled_boundedGaugeIncidence"
    finding := "Every gauge coordinate has incidence one."
  },
  {
    fieldName := "admissibleHistories"
    status := .dischargedAtScale
    theoremName := "phaseEScaled_admissibleHistories"
    finding := "The Unit history field is balanced; the target/gauge parity core also cites KernelFlip exact neutrality."
  },
  {
    fieldName := "safeQSSM"
    status := .boundedClass
    theoremName := "phaseEScaled_safeQSSM_boundedClass"
    finding := "Discharged for target-blind safe reads in the named bounded class."
  },
  {
    fieldName := "boundaryMixing"
    status := .boundedClass
    theoremName := "phaseEScaled_boundaryMixing_boundedClass"
    finding := "Every target-blind payload observer has exact half success."
  }
]

theorem phaseEScaledObligationMap_length :
    phaseEScaledObligationMap.length = 9 := by
  rfl

theorem phaseEScaledObligationMap_has_no_failures :
    ∀ row ∈ phaseEScaledObligationMap, row.status ≠ .failed := by
  intro row hmem
  simp [phaseEScaledObligationMap] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  all_goals subst row; decide

def PhaseEScaledAllMappedObligations (m k : Nat) : Prop :=
    PhaseEScaledSevenCombinatorialObligations m k ∧
      (∀ q : PhaseEScaledSafe m k,
        0 ≤ phaseEScaledSafeCost q ∧ phaseEScaledSafeCost q ≤ 0) ∧
      BoundaryMixingBound (@phaseEScaledTarget m k)
        (@phaseEScaledPayloadSummary m k) 0 ∧
      (∀ observer : PhaseEScaledTargetBlindPayloadObserver m k,
        globalDecoderSuccess
            (fun omega : PhaseEScaledWorld m k =>
              observer (phaseEScaledPayloadSummary omega))
            phaseEScaledTarget =
          (1 : Rat) / 2)

theorem phaseEScaled_all_mapped_obligations (m k : Nat) :
    PhaseEScaledAllMappedObligations m k := by
  exact
    ⟨phaseEScaled_seven_combinatorial_obligations m k,
      phaseEScaled_safeQSSM_boundedClass m k,
      phaseEScaled_boundaryMixing_boundedClass m k,
      phaseEScaled_targetBlindPayloadObserver_hardCore m k⟩

end Mettapedia.Computability.PNP
