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
  W.quotient = (W.rawWitness ^^ W.hiddenGauge)

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

/-! ## P=NP-conditional self-reduction model for the toy -/

/--
Restricted SAT instances for the toy bit-fixing search.  This is the toy
analogue of the manuscript's restricted CNF formulas `F[a]`: each constructor
fixes a longer prefix in the canonical witness-variable order
`rawWitness, hiddenGauge, quotient, message`.
-/
inductive V14ToyRestrictedFormula where
  | unrestricted (Y : V14ToyPublic)
  | withRaw (Y : V14ToyPublic) (rawWitness : Bool)
  | withRawHidden
      (Y : V14ToyPublic) (rawWitness hiddenGauge : Bool)
  | withRawHiddenQuotient
      (Y : V14ToyPublic) (rawWitness hiddenGauge quotient : Bool)
  | complete
      (Y : V14ToyPublic)
      (rawWitness hiddenGauge quotient message : Bool)
deriving DecidableEq, Repr

def v14ToyRestrictedFormulaSatisfiable :
    V14ToyRestrictedFormula -> Prop
  | .unrestricted Y =>
      ∃ W, v14ToyLockedVerifier Y W
  | .withRaw Y rawWitness =>
      ∃ W,
        v14ToyLockedVerifier Y W ∧
          W.rawWitness = rawWitness
  | .withRawHidden Y rawWitness hiddenGauge =>
      ∃ W,
        v14ToyLockedVerifier Y W ∧
          W.rawWitness = rawWitness ∧
            W.hiddenGauge = hiddenGauge
  | .withRawHiddenQuotient Y rawWitness hiddenGauge quotient =>
      ∃ W,
        v14ToyLockedVerifier Y W ∧
          W.rawWitness = rawWitness ∧
            W.hiddenGauge = hiddenGauge ∧
              W.quotient = quotient
  | .complete Y rawWitness hiddenGauge quotient message =>
      ∃ W,
        v14ToyLockedVerifier Y W ∧
          W.rawWitness = rawWitness ∧
            W.hiddenGauge = hiddenGauge ∧
              W.quotient = quotient ∧
                W.message = message

/--
Explicit P=NP-side hypothesis object for the toy.  It records a fixed
polynomial-time SAT decider for all restricted toy instances, together with
the source length and clock exponent that are charged to the constant decoder.
The generic universal-machine semantics of `Kpoly` is not formalized here;
the toy uses these two natural-number fields as its concrete constant decoder
cost model.
-/
structure V14ToyPNPSATDecider where
  decideSat : V14ToyRestrictedFormula -> Bool
  decidesSat :
    ∀ F, decideSat F = true ↔ v14ToyRestrictedFormulaSatisfiable F
  programLength : Nat
  clockExponent : Nat
  clockExponent_pos : 0 < clockExponent

theorem v14ToyRestricted_withRawHiddenQuotient_satisfiable_iff
    (Y : V14ToyPublic) (rawWitness hiddenGauge quotient : Bool) :
    v14ToyRestrictedFormulaSatisfiable
        (.withRawHiddenQuotient Y rawWitness hiddenGauge quotient) ↔
      quotient = (rawWitness ^^ hiddenGauge) := by
  constructor
  · intro hSat
    rcases hSat with ⟨W, hVerifier, hRaw, hHidden, hQuotient⟩
    rcases hVerifier with ⟨hGauge, _hMessage⟩
    rw [← hQuotient, hGauge, hRaw, hHidden]
  · intro hQuotient
    refine
      ⟨{ rawWitness := rawWitness
         hiddenGauge := hiddenGauge
         quotient := quotient
         message := v14ToyMessageOfPublic Y },
        ?_⟩
    simp [v14ToyLockedVerifier, v14ToyGaugeEq, hQuotient]

theorem v14ToyRestricted_complete_satisfiable_iff
    (Y : V14ToyPublic)
    (rawWitness hiddenGauge quotient message : Bool) :
    v14ToyRestrictedFormulaSatisfiable
        (.complete Y rawWitness hiddenGauge quotient message) ↔
      quotient = (rawWitness ^^ hiddenGauge) ∧
        message = v14ToyMessageOfPublic Y := by
  constructor
  · intro hSat
    rcases hSat with
      ⟨W, hVerifier, hRaw, hHidden, hQuotient, hMessageFixed⟩
    rcases hVerifier with ⟨hGauge, hMessage⟩
    constructor
    · rw [← hQuotient, hGauge, hRaw, hHidden]
    · rw [← hMessageFixed, hMessage]
  · intro h
    refine
      ⟨{ rawWitness := rawWitness
         hiddenGauge := hiddenGauge
         quotient := quotient
         message := message },
        ?_⟩
    simp [v14ToyLockedVerifier, v14ToyGaugeEq, h.1, h.2]

def v14ToyBitFixRaw
    (D : V14ToyPNPSATDecider) (Y : V14ToyPublic) : Bool :=
  if D.decideSat (.withRaw Y false) then false else true

def v14ToyBitFixHidden
    (D : V14ToyPNPSATDecider) (Y : V14ToyPublic)
    (rawWitness : Bool) : Bool :=
  if D.decideSat (.withRawHidden Y rawWitness false) then false else true

def v14ToyBitFixQuotient
    (D : V14ToyPNPSATDecider) (Y : V14ToyPublic)
    (rawWitness hiddenGauge : Bool) : Bool :=
  if D.decideSat
      (.withRawHiddenQuotient Y rawWitness hiddenGauge false)
    then false
    else true

def v14ToyBitFixMessage
    (D : V14ToyPNPSATDecider) (Y : V14ToyPublic)
    (rawWitness hiddenGauge quotient : Bool) : Bool :=
  if D.decideSat
      (.complete Y rawWitness hiddenGauge quotient false)
    then false
    else true

theorem v14ToyBitFixQuotient_satisfiable
    (D : V14ToyPNPSATDecider) (Y : V14ToyPublic)
    (rawWitness hiddenGauge : Bool) :
    v14ToyRestrictedFormulaSatisfiable
      (.withRawHiddenQuotient Y rawWitness hiddenGauge
        (v14ToyBitFixQuotient D Y rawWitness hiddenGauge)) := by
  unfold v14ToyBitFixQuotient
  by_cases hDec :
      D.decideSat
          (.withRawHiddenQuotient Y rawWitness hiddenGauge false) =
        true
  · simp [hDec]
    exact (D.decidesSat _).mp hDec
  · simp [hDec]
    rw [v14ToyRestricted_withRawHiddenQuotient_satisfiable_iff]
    have hNotSat :
        ¬ v14ToyRestrictedFormulaSatisfiable
          (.withRawHiddenQuotient Y rawWitness hiddenGauge false) := by
      intro hSat
      exact hDec ((D.decidesSat _).mpr hSat)
    rw [v14ToyRestricted_withRawHiddenQuotient_satisfiable_iff] at hNotSat
    cases rawWitness <;> cases hiddenGauge <;> simp at hNotSat ⊢

theorem v14ToyBitFixMessage_satisfiable
    (D : V14ToyPNPSATDecider) (Y : V14ToyPublic)
    (rawWitness hiddenGauge quotient : Bool)
    (hPrefix :
      v14ToyRestrictedFormulaSatisfiable
        (.withRawHiddenQuotient Y rawWitness hiddenGauge quotient)) :
    v14ToyRestrictedFormulaSatisfiable
      (.complete Y rawWitness hiddenGauge quotient
        (v14ToyBitFixMessage D Y rawWitness hiddenGauge quotient)) := by
  unfold v14ToyBitFixMessage
  by_cases hDec :
      D.decideSat
          (.complete Y rawWitness hiddenGauge quotient false) =
        true
  · simp [hDec]
    exact (D.decidesSat _).mp hDec
  · simp [hDec]
    rw [v14ToyRestricted_complete_satisfiable_iff]
    have hNotSat :
        ¬ v14ToyRestrictedFormulaSatisfiable
          (.complete Y rawWitness hiddenGauge quotient false) := by
      intro hSat
      exact hDec ((D.decidesSat _).mpr hSat)
    have hQuotient :
        quotient = (rawWitness ^^ hiddenGauge) :=
      (v14ToyRestricted_withRawHiddenQuotient_satisfiable_iff
        Y rawWitness hiddenGauge quotient).mp hPrefix
    have hMessageNotFalse :
        ¬ false = v14ToyMessageOfPublic Y := by
      intro hMessageFalse
      exact hNotSat
        ((v14ToyRestricted_complete_satisfiable_iff
          Y rawWitness hiddenGauge quotient false).mpr
          ⟨hQuotient, hMessageFalse⟩)
    constructor
    · exact hQuotient
    · cases hMessage : v14ToyMessageOfPublic Y
      · exact False.elim (hMessageNotFalse (by simp [hMessage]))
      · rfl

def v14ToySelfReductionWitness
    (D : V14ToyPNPSATDecider) (Y : V14ToyPublic) : V14ToyWitness :=
  let rawWitness := v14ToyBitFixRaw D Y
  let hiddenGauge := v14ToyBitFixHidden D Y rawWitness
  let quotient := v14ToyBitFixQuotient D Y rawWitness hiddenGauge
  let message := v14ToyBitFixMessage D Y rawWitness hiddenGauge quotient
  { rawWitness := rawWitness
    hiddenGauge := hiddenGauge
    quotient := quotient
    message := message }

theorem v14ToySelfReductionWitness_satisfies
    (D : V14ToyPNPSATDecider) (Y : V14ToyPublic) :
    v14ToyLockedVerifier Y (v14ToySelfReductionWitness D Y) := by
  let rawWitness := v14ToyBitFixRaw D Y
  let hiddenGauge := v14ToyBitFixHidden D Y rawWitness
  let quotient := v14ToyBitFixQuotient D Y rawWitness hiddenGauge
  let message := v14ToyBitFixMessage D Y rawWitness hiddenGauge quotient
  have hPrefix :
      v14ToyRestrictedFormulaSatisfiable
        (.withRawHiddenQuotient Y rawWitness hiddenGauge quotient) :=
    v14ToyBitFixQuotient_satisfiable D Y rawWitness hiddenGauge
  have hComplete :
      v14ToyRestrictedFormulaSatisfiable
        (.complete Y rawWitness hiddenGauge quotient message) :=
    v14ToyBitFixMessage_satisfiable
      D Y rawWitness hiddenGauge quotient hPrefix
  have hFields :
      quotient = (rawWitness ^^ hiddenGauge) ∧
        message = v14ToyMessageOfPublic Y :=
    (v14ToyRestricted_complete_satisfiable_iff
      Y rawWitness hiddenGauge quotient message).mp hComplete
  change
    v14ToyLockedVerifier Y
      { rawWitness := rawWitness
        hiddenGauge := hiddenGauge
        quotient := quotient
        message := message }
  exact hFields

theorem v14ToySelfReduction_readout_eq_message
    (D : V14ToyPNPSATDecider) (Y : V14ToyPublic) :
    v14ToyMessageReadout (v14ToySelfReductionWitness D Y) =
      v14ToyMessageOfPublic Y :=
  (v14ToySelfReductionWitness_satisfies D Y).2

theorem v14ToySelfReduction_readout_eq_validWitness_readout
    (D : V14ToyPNPSATDecider) (Y : V14ToyPublic) (W : V14ToyWitness)
    (hW : v14ToyLockedVerifier Y W) :
    v14ToyMessageReadout (v14ToySelfReductionWitness D Y) =
      v14ToyMessageReadout W :=
  v14ToyVerifier_singleMessage Y
    (v14ToySelfReductionWitness D Y) W
    (v14ToySelfReductionWitness_satisfies D Y) hW

def v14ToyRestrictedFormulaCompilerProgramLength : Nat :=
  1

def v14ToySelfReductionDriverProgramLength : Nat :=
  1

def v14ToyReadoutProgramLength : Nat :=
  1

def v14ToySelfReductionDecoderCost
    (D : V14ToyPNPSATDecider) : Nat :=
  D.programLength +
    v14ToyRestrictedFormulaCompilerProgramLength +
      v14ToySelfReductionDriverProgramLength +
        v14ToyReadoutProgramLength

def v14ToyConstantDecoderKpolyAt
    (D : V14ToyPNPSATDecider) : Nat -> Nat :=
  fun _targetBlocks => v14ToySelfReductionDecoderCost D

def v14ToyLinearEtaTimes (eta : Nat) : Nat -> Nat :=
  fun targetBlocks => eta * targetBlocks

theorem v14ToyConstantDecoderKpolyAt_eq
    (D : V14ToyPNPSATDecider) (targetBlocks : Nat) :
    v14ToyConstantDecoderKpolyAt D targetBlocks =
      v14ToySelfReductionDecoderCost D :=
  rfl

theorem v14Toy_constantDecoder_lt_linearFloor
    (D : V14ToyPNPSATDecider) {eta targetBlocks : Nat}
    (hFloor :
      v14ToySelfReductionDecoderCost D < eta * targetBlocks) :
    v14ToyConstantDecoderKpolyAt D targetBlocks <
      v14ToyLinearEtaTimes eta targetBlocks := by
  simpa [v14ToyConstantDecoderKpolyAt, v14ToyLinearEtaTimes] using hFloor

/--
Concrete target-block regime for the toy upper side: the lower framework's
abstract `kpolyAt` is identified with the constant self-reduction decoder cost,
and its abstract `etaTimes` is identified with the linear floor `eta * t`.
-/
structure V14ToyConstantDecoderRegime
    (F : CompressionLowerFramework) (D : V14ToyPNPSATDecider) where
  eta : Nat
  kpolyAt_eq : F.kpolyAt = v14ToyConstantDecoderKpolyAt D
  etaTimes_eq : F.etaTimes = v14ToyLinearEtaTimes eta
  floor_dominates_decoder :
    v14ToySelfReductionDecoderCost D < eta * F.targetBlocks

/--
The construction-side discharge of `SelfReductionUpperHypothesis` for the toy,
given the explicit P=NP SAT decider object and the concrete constant-vs-linear
target-block regime.  This is only the P=NP-conditional upper side.
-/
theorem v14Toy_selfReductionUpperHypothesis_givenPNP
    {F : CompressionLowerFramework} (D : V14ToyPNPSATDecider)
    (R : V14ToyConstantDecoderRegime F D) :
    SelfReductionUpperHypothesis F where
  upperStrictlyBelowCompressionFloor := by
    rw [R.kpolyAt_eq, R.etaTimes_eq]
    exact R.floor_dominates_decoder

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

structure SafeQSSMFrontier : Prop where
  safeQSSM :
    ∀ q : V14ToySafe,
      0 ≤ v14ToySafeCost q ∧ v14ToySafeCost q ≤ v14ToySafeBudget

structure BoundedGaugeIncidenceFrontier : Prop where
  boundedGaugeIncidence :
    ∀ gamma : V14ToyGauge,
      v14ToyGaugeIncidence gamma ≤ v14ToyGaugeBound

structure BoundaryMixingFrontier : Prop where
  boundaryMixing :
    BoundaryMixingBound v14ToyTarget v14ToyPivot v14ToyEpsMix

structure V14ToyAnalyticFrontier : Prop where
  safeQSSM : SafeQSSMFrontier
  boundedGaugeIncidence : BoundedGaugeIncidenceFrontier
  boundaryMixing : BoundaryMixingFrontier

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
  gaugePredicateTotal := v14ToyInterfaceHiddenGaugeProduct
  noPublicTargetTags := v14ToyNoPublicTargetTags
  atomCompleteness := v14ToyAtomCompleteness
  gaugeFaithfulness := v14ToyGaugeFaithfulness
  safeQSSM := A.safeQSSM.safeQSSM
  boundedGaugeIncidence := A.boundedGaugeIncidence.boundedGaugeIncidence
  boundaryMixing := A.boundaryMixing.boundaryMixing
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

structure V14ToyStructuralFieldsConstructed : Prop where
  singleMessage :
    ∀ w0 w1 : V14ToyWorld,
      v14ToyPublicInput w0 = v14ToyPublicInput w1 ->
        v14ToyTarget w0 = v14ToyTarget w1
  gaugePredicateTotal :
    ∀ gamma omega, v14ToySemantics.gaugeSat gamma omega
  noPublicTargetTags :
    PairNeutral v14ToyOppositeSupport v14ToyNeutralSkeleton ∧
      HasMessageOppositePair v14ToyOppositeSupport v14ToyTarget ∧
        ¬ ∃ f : Unit -> Bool,
          ∀ omega, v14ToyTarget omega = f (v14ToyNeutralSkeleton omega)
  atomCompleteness :
    ∀ E : RawEvidence V14ToyNeutral V14ToySafe V14ToyGauge,
      v14ToySemantics.SatNormal (CDENF E) = v14ToySemantics.SatRaw E
  gaugeFaithfulness :
    ∀ gamma : V14ToyGauge,
      v14ToySemantics.SatNormal (CDENF (.gauge gamma)) =
        v14ToySemantics.gaugeSat gamma
  admissibleHistories :
    BalancedBit v14ToyTarget ∧
      BalancedConditioning v14ToyHistoryField v14ToyTarget

theorem v14Toy_structuralFields_constructed :
    V14ToyStructuralFieldsConstructed where
  singleMessage := v14ToySingleMessage
  gaugePredicateTotal := v14ToyInterfaceHiddenGaugeProduct
  noPublicTargetTags := v14ToyNoPublicTargetTags
  atomCompleteness := v14ToyAtomCompleteness
  gaugeFaithfulness := v14ToyGaugeFaithfulness
  admissibleHistories := v14ToyHistory_admissible

structure V14ToyAnalyticFieldsCarried
    (A : V14ToyAnalyticFrontier) : Prop where
  safeQSSM : SafeQSSMFrontier
  boundedGaugeIncidence : BoundedGaugeIncidenceFrontier
  boundaryMixing : BoundaryMixingFrontier

theorem v14Toy_analyticFields_carried
    (A : V14ToyAnalyticFrontier) :
    V14ToyAnalyticFieldsCarried A where
  safeQSSM := A.safeQSSM
  boundedGaugeIncidence := A.boundedGaugeIncidence
  boundaryMixing := A.boundaryMixing

structure V14ToyResidualOpenInputs
    {A : V14ToyAnalyticFrontier}
    (P : ParameterRecord (v14ToyLockedInterface A)) : Prop where
  starSWHardness_audited :
    (v13ParameterRecordAudit.get ⟨5, by decide⟩).status =
      ParameterFieldStatus.openInput
  starSWHardness : CompressionStarSWHardness P.lowerFramework

theorem v14Toy_residualOpenInputs
    {A : V14ToyAnalyticFrontier}
    (P : ParameterRecord (v14ToyLockedInterface A)) :
    V14ToyResidualOpenInputs P where
  starSWHardness_audited := by
    simp [v13ParameterRecordAudit]
  starSWHardness := P.starSWHardness

structure V14ToyParameterPayloadAudited
    {A : V14ToyAnalyticFrontier}
    (P : ParameterRecord (v14ToyLockedInterface A)) : Prop where
  fixedGapBudget_audited :
    (v13ParameterRecordAudit.get ⟨0, by decide⟩).status =
      ParameterFieldStatus.numeric
  phaseABudget_audited :
    (v13ParameterRecordAudit.get ⟨1, by decide⟩).status =
      ParameterFieldStatus.numeric
  phaseABudget :
    (1 / 2 : Rat) *
        (v14ToyLockedInterface A).phaseA.telescoping.derivativeSum ≤
      P.fixedGapBudget
  epsSmall_audited :
    (v13ParameterRecordAudit.get ⟨2, by decide⟩).status =
      ParameterFieldStatus.numeric
  epsSmall : (v14ToyLockedInterface A).epsMix < (1 / 2 : Rat)
  lowerFramework_audited :
    (v13ParameterRecordAudit.get ⟨3, by decide⟩).status =
      ParameterFieldStatus.derived
  kernelNeutrality_audited :
    (v13ParameterRecordAudit.get ⟨4, by decide⟩).status =
      ParameterFieldStatus.derived
  kernelNeutrality : CompressionKernelNeutrality P.lowerFramework

theorem v14Toy_parameterPayload_audited
    {A : V14ToyAnalyticFrontier}
    (P : ParameterRecord (v14ToyLockedInterface A)) :
    V14ToyParameterPayloadAudited P where
  fixedGapBudget_audited := by
    simp [v13ParameterRecordAudit]
  phaseABudget_audited := by
    simp [v13ParameterRecordAudit]
  phaseABudget := P.phaseABudget
  epsSmall_audited := by
    simp [v13ParameterRecordAudit]
  epsSmall := P.epsSmall
  lowerFramework_audited := by
    simp [v13ParameterRecordAudit]
  kernelNeutrality_audited := by
    simp [v13ParameterRecordAudit]
  kernelNeutrality := P.kernelNeutrality

def v14ToyParameterRecordWithPNPUpper
    {A : V14ToyAnalyticFrontier}
    (P : ParameterRecord (v14ToyLockedInterface A))
    (D : V14ToyPNPSATDecider)
    (R : V14ToyConstantDecoderRegime P.lowerFramework D) :
    ParameterRecord (v14ToyLockedInterface A) :=
  { P with
    selfReductionUpper :=
      v14Toy_selfReductionUpperHypothesis_givenPNP D R }

structure V14ToyExactFrontierUse
    (A : V14ToyAnalyticFrontier)
    (P : ParameterRecord (v14ToyLockedInterface A)) : Prop where
  structural : V14ToyStructuralFieldsConstructed
  analytic : V14ToyAnalyticFieldsCarried A
  parameterPayload : V14ToyParameterPayloadAudited P
  residualOpen : V14ToyResidualOpenInputs P
  selfReductionUpper : SelfReductionUpperHypothesis P.lowerFramework
  conclusion : UpperLowerClash (v14ToyLockedInterface A) P

theorem v14Toy_reduction_uses_exact_analytic_frontier
    (A : V14ToyAnalyticFrontier)
    (P : ParameterRecord (v14ToyLockedInterface A)) :
    V14ToyExactFrontierUse A P where
  structural := v14Toy_structuralFields_constructed
  analytic := v14Toy_analyticFields_carried A
  parameterPayload := v14Toy_parameterPayload_audited P
  residualOpen := v14Toy_residualOpenInputs P
  selfReductionUpper := P.selfReductionUpper
  conclusion := v14Toy_structuralReduction A P

theorem v14Toy_reduction_uses_exact_analytic_frontier_givenPNP
    (A : V14ToyAnalyticFrontier)
    (P : ParameterRecord (v14ToyLockedInterface A))
    (D : V14ToyPNPSATDecider)
    (R : V14ToyConstantDecoderRegime P.lowerFramework D) :
    V14ToyExactFrontierUse A
      (v14ToyParameterRecordWithPNPUpper P D R) where
  structural := v14Toy_structuralFields_constructed
  analytic := v14Toy_analyticFields_carried A
  parameterPayload :=
    v14Toy_parameterPayload_audited
      (v14ToyParameterRecordWithPNPUpper P D R)
  residualOpen :=
    v14Toy_residualOpenInputs
      (v14ToyParameterRecordWithPNPUpper P D R)
  selfReductionUpper :=
    v14Toy_selfReductionUpperHypothesis_givenPNP D R
  conclusion :=
    v14Toy_structuralReduction A
      (v14ToyParameterRecordWithPNPUpper P D R)

def v14ToyReductionStatement : String :=
  "With singleMessage, noPublicTargetTags, atomCompleteness, gaugeFaithfulness, gaugePredicateTotal, and admissibleHistories construction-proved for the v14 toy, and with SelfReductionUpperHypothesis construction-proved given an explicit V14ToyPNPSATDecider plus the constant-decoder regime, the residual open inputs are ParameterRecord.starSWHardness together with SafeQSSMFrontier.safeQSSM, BoundedGaugeIncidenceFrontier.boundedGaugeIncidence, and BoundaryMixingFrontier.boundaryMixing; the Lean conclusion remains UpperLowerClash for the ParameterRecord whose selfReductionUpper field is v14Toy_selfReductionUpperHypothesis_givenPNP."

/-! ## Weak-frontier canaries -/

structure SafeQSSMFull
    (Probe : Type) (cost : Probe -> Rat) (budget : Rat) : Prop where
  safeQSSM : ∀ q : Probe, 0 ≤ cost q ∧ cost q ≤ budget

structure SafeQSSMNonnegativeOnly
    (Probe : Type) (cost : Probe -> Rat) : Prop where
  nonnegative : ∀ q : Probe, 0 ≤ cost q

inductive SafeQSSMCanaryProbe where
  | q
deriving DecidableEq, Repr

def safeQSSMCanaryCost (_q : SafeQSSMCanaryProbe) : Rat :=
  1

def safeQSSMCanaryBudget : Rat :=
  0

theorem safeQSSM_weakened_frontier_insufficient :
    SafeQSSMNonnegativeOnly SafeQSSMCanaryProbe safeQSSMCanaryCost ∧
      ¬ SafeQSSMFull SafeQSSMCanaryProbe safeQSSMCanaryCost
        safeQSSMCanaryBudget := by
  constructor
  · exact
      { nonnegative := by
          intro probe
          cases probe
          norm_num [safeQSSMCanaryCost] }
  · intro hFull
    have hq := hFull.safeQSSM SafeQSSMCanaryProbe.q
    norm_num [safeQSSMCanaryCost, safeQSSMCanaryBudget] at hq

structure GaugeIncidenceFull
    (Gauge : Type) (incidence : Gauge -> Nat) (bound : Nat) : Prop where
  boundedGaugeIncidence : ∀ gamma : Gauge, incidence gamma ≤ bound

structure GaugeIncidenceSelfBoundOnly
    (Gauge : Type) (incidence : Gauge -> Nat) : Prop where
  selfBound : ∀ gamma : Gauge, incidence gamma ≤ incidence gamma

inductive GaugeIncidenceCanary where
  | gamma
deriving DecidableEq, Repr

def gaugeIncidenceCanaryIncidence (_gamma : GaugeIncidenceCanary) : Nat :=
  1

def gaugeIncidenceCanaryBound : Nat :=
  0

theorem boundedGaugeIncidence_weakened_frontier_insufficient :
    GaugeIncidenceSelfBoundOnly GaugeIncidenceCanary
        gaugeIncidenceCanaryIncidence ∧
      ¬ GaugeIncidenceFull GaugeIncidenceCanary
        gaugeIncidenceCanaryIncidence gaugeIncidenceCanaryBound := by
  constructor
  · exact
      { selfBound := by
          intro charge
          rfl }
  · intro hFull
    have hgamma := hFull.boundedGaugeIncidence GaugeIncidenceCanary.gamma
    norm_num [gaugeIncidenceCanaryIncidence, gaugeIncidenceCanaryBound] at hgamma

def BoundaryMixingBalancedOnly
    {Omega : Type} [Fintype Omega] (target : Omega -> Bool) : Prop :=
  BalancedBit target

theorem boundaryMixing_weakened_frontier_insufficient :
    BoundaryMixingBalancedOnly v14ToyTarget ∧
      ¬ BoundaryMixingBound v14ToyTarget v14ToyTarget 0 := by
  constructor
  · exact v14ToyTarget_balanced
  · intro hMix
    have hHalf : (1 / 2 : Rat) ≤ 0 :=
      sufficient_boundary_feature_forces_eps_ge_half
        v14ToyTarget v14ToyTarget
        v14ToyTarget_balanced
        ⟨fun z => z, by intro omega; rfl⟩
        hMix
    norm_num at hHalf

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
    item := "field gaugePredicateTotal"
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
    checkedName := "SafeQSSMFrontier.safeQSSM"
    note := "Quantitative safe-buffer leakage is intentionally carried."
  },
  {
    item := "field boundedGaugeIncidence"
    status := .carriedAnalyticFrontier
    checkedName := "BoundedGaugeIncidenceFrontier.boundedGaugeIncidence"
    note := "Gauge-incidence/rank control is intentionally carried."
  },
  {
    item := "field boundaryMixing"
    status := .carriedAnalyticFrontier
    checkedName := "BoundaryMixingFrontier.boundaryMixing"
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

/-! ## Exact-use ledger -/

inductive V14ExactUseLedgerStatus where
  | structuralProved
  | analyticCarried
  | constructionProvedGivenPNP
  | residualOpenInput
deriving DecidableEq, Repr

structure V14ExactUseLedgerRow where
  item : String
  status : V14ExactUseLedgerStatus
  checkedName : String
deriving Repr

def v14ToyExactUseLedger : List V14ExactUseLedgerRow := [
  {
    item := "singleMessage"
    status := .structuralProved
    checkedName := "V14ToyStructuralFieldsConstructed.singleMessage"
  },
  {
    item := "gaugePredicateTotal"
    status := .structuralProved
    checkedName := "V14ToyStructuralFieldsConstructed.gaugePredicateTotal"
  },
  {
    item := "noPublicTargetTags"
    status := .structuralProved
    checkedName := "V14ToyStructuralFieldsConstructed.noPublicTargetTags"
  },
  {
    item := "atomCompleteness"
    status := .structuralProved
    checkedName := "V14ToyStructuralFieldsConstructed.atomCompleteness"
  },
  {
    item := "gaugeFaithfulness"
    status := .structuralProved
    checkedName := "V14ToyStructuralFieldsConstructed.gaugeFaithfulness"
  },
  {
    item := "admissibleHistories"
    status := .structuralProved
    checkedName := "V14ToyStructuralFieldsConstructed.admissibleHistories"
  },
  {
    item := "safeQSSM"
    status := .analyticCarried
    checkedName := "SafeQSSMFrontier.safeQSSM"
  },
  {
    item := "boundedGaugeIncidence"
    status := .analyticCarried
    checkedName := "BoundedGaugeIncidenceFrontier.boundedGaugeIncidence"
  },
  {
    item := "boundaryMixing"
    status := .analyticCarried
    checkedName := "BoundaryMixingFrontier.boundaryMixing"
  },
  {
    item := "selfReductionUpper"
    status := .constructionProvedGivenPNP
    checkedName := "v14Toy_selfReductionUpperHypothesis_givenPNP"
  },
  {
    item := "starSWHardness"
    status := .residualOpenInput
    checkedName := "ParameterRecord.starSWHardness"
  }
]

theorem v14ToyExactUseLedger_length :
    v14ToyExactUseLedger.length = 11 := by
  rfl

theorem v14ToyExactUseLedger_structural_proved :
    (v14ToyExactUseLedger.get ⟨0, by decide⟩).status =
        V14ExactUseLedgerStatus.structuralProved ∧
      (v14ToyExactUseLedger.get ⟨1, by decide⟩).status =
        V14ExactUseLedgerStatus.structuralProved ∧
      (v14ToyExactUseLedger.get ⟨2, by decide⟩).status =
        V14ExactUseLedgerStatus.structuralProved ∧
      (v14ToyExactUseLedger.get ⟨3, by decide⟩).status =
        V14ExactUseLedgerStatus.structuralProved ∧
      (v14ToyExactUseLedger.get ⟨4, by decide⟩).status =
        V14ExactUseLedgerStatus.structuralProved ∧
      (v14ToyExactUseLedger.get ⟨5, by decide⟩).status =
        V14ExactUseLedgerStatus.structuralProved := by
  simp [v14ToyExactUseLedger]

theorem v14ToyExactUseLedger_analytic_carried :
    (v14ToyExactUseLedger.get ⟨6, by decide⟩).status =
        V14ExactUseLedgerStatus.analyticCarried ∧
      (v14ToyExactUseLedger.get ⟨7, by decide⟩).status =
        V14ExactUseLedgerStatus.analyticCarried ∧
      (v14ToyExactUseLedger.get ⟨8, by decide⟩).status =
        V14ExactUseLedgerStatus.analyticCarried := by
  simp [v14ToyExactUseLedger]

theorem v14ToyExactUseLedger_selfReduction_upper_constructed_givenPNP :
    (v14ToyExactUseLedger.get ⟨9, by decide⟩).status =
      V14ExactUseLedgerStatus.constructionProvedGivenPNP := by
  rfl

theorem v14ToyExactUseLedger_residual_open_inputs :
    (v14ToyExactUseLedger.get ⟨6, by decide⟩).status =
        V14ExactUseLedgerStatus.analyticCarried ∧
      (v14ToyExactUseLedger.get ⟨7, by decide⟩).status =
        V14ExactUseLedgerStatus.analyticCarried ∧
      (v14ToyExactUseLedger.get ⟨8, by decide⟩).status =
        V14ExactUseLedgerStatus.analyticCarried ∧
      (v14ToyExactUseLedger.get ⟨10, by decide⟩).status =
        V14ExactUseLedgerStatus.residualOpenInput := by
  simp [v14ToyExactUseLedger]

end Mettapedia.Computability.PNP
