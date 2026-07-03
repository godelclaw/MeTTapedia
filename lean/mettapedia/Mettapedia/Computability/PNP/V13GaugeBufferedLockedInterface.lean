import Mettapedia.Computability.PNP.PublicNeutralityRedTeam
import Mettapedia.Computability.PNP.V13CDENF
import Mettapedia.Computability.PNP.V13EvidenceSpine

/-!
# PNP v13 gauge-buffered locked interface ledger

This module packages the abstract v13 assumptions as real propositions about
the Phase A finite spine and Phase B CD-ENF objects.  It also includes the
critical non-vacuity test: a small toy jointly inhabits all nine fields.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u v w x y z a b c d e f

structure GaugeBufferedLockedInterface
    (Omega : Type u) [Fintype Omega] [Nonempty Omega]
    (Public : Type v) (Neutral : Type w) (Safe : Type x) (Gauge : Type y)
    (Transcript : Type z) [DecidableEq Transcript]
    (Pair : Type a) [Fintype Pair]
    (Stage : Type b) (Branch : Type c)
    (HistoryAtom : Type d) (Pivot : Type e)
    (Observer : Type f) (Output : Type f) (Skeleton : Type w) where
  law : FiniteRationalLaw Omega
  target : Omega -> Bool
  publicInput : Omega -> Public
  neutralSkeleton : Omega -> Skeleton
  oppositeSupport : Omega -> Omega -> Prop
  transcript : Omega -> Transcript
  observerBit : Transcript -> Bool
  phaseA :
    EvidenceSpineBound law target transcript observerBit Pair Stage Branch
  semantics : EvidenceSemantics Omega Neutral Safe Gauge
  observerEvidence :
    ObserverEvidenceInterface Omega Public Observer Output Neutral Safe Gauge
  historyField : FiniteSigmaField.{u, d} Omega
  pivotSummary : Omega -> Pivot
  epsMix : Rat
  safeCost : Safe -> Rat
  safeBudget : Rat
  gaugeIncidence : Gauge -> Nat
  gaugeBound : Nat
  singleMessage :
    ∀ w0 w1, publicInput w0 = publicInput w1 -> target w0 = target w1
  hiddenGaugeProduct :
    ∀ gamma omega, semantics.gaugeSat gamma omega
  noPublicTargetTags :
    PairNeutral oppositeSupport neutralSkeleton ∧
      HasMessageOppositePair oppositeSupport target ∧
        ¬ ∃ f : Skeleton -> Bool, ∀ omega, target omega = f (neutralSkeleton omega)
  atomCompleteness :
    ∀ E : RawEvidence Neutral Safe Gauge,
      semantics.SatNormal (CDENF E) = semantics.SatRaw E
  gaugeFaithfulness :
    ∀ gamma : Gauge,
      semantics.SatNormal (CDENF (.gauge gamma)) =
        semantics.gaugeSat gamma
  safeQSSM :
    ∀ q : Safe, 0 ≤ safeCost q ∧ safeCost q ≤ safeBudget
  boundedGaugeIncidence :
    ∀ gamma : Gauge, gaugeIncidence gamma ≤ gaugeBound
  boundaryMixing :
    BoundaryMixingBound target pivotSummary epsMix
  admissibleHistories :
    BalancedBit target ∧ BalancedConditioning (Omega := Omega) historyField target

namespace GaugeBufferedLockedInterface

variable {Omega : Type u} [Fintype Omega] [Nonempty Omega]
variable {Public : Type v} {Neutral : Type w} {Safe : Type x}
variable {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
variable {Pair : Type a} [Fintype Pair] {Stage : Type b} {Branch : Type c}
variable {HistoryAtom : Type d} {Pivot : Type e}
variable {Observer : Type f} {Output : Type f} {Skeleton : Type w}

/-- Ledger coherence: an admissible history cannot also make the target
measurable, once the target is nondegenerate. -/
theorem admissible_history_not_target_measurable
    (L : GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (hNondeg : NontrivialWitnessBit L.target) :
    ¬ MeasurableWrt L.historyField L.target := by
  intro hMeas
  exact
    measurable_not_admissible
      L.target L.historyField hMeas hNondeg L.admissibleHistories.2

/-- Ledger coherence: if the boundary mixing error is strictly below one half,
the pivot summary cannot be sufficient for the target. -/
theorem boundary_mixing_blocks_pivot_sufficiency
    (L : GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (hSmall : L.epsMix < (1 / 2 : Rat)) :
    ¬ ∃ h0 : Pivot -> Bool, ∀ omega, L.target omega = h0 (L.pivotSummary omega) := by
  intro hSuff
  have hHalf : (1 / 2 : Rat) ≤ L.epsMix :=
    sufficient_boundary_feature_forces_eps_ge_half
      L.target L.pivotSummary L.admissibleHistories.1 hSuff L.boundaryMixing
  linarith

/-- Ledger coherence: the neutral skeleton field itself gives the red-team
non-sufficiency verdict. -/
theorem neutral_skeleton_not_target_sufficient
    (L : GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton) :
    ¬ ∃ f : Skeleton -> Bool, ∀ omega, L.target omega = f (L.neutralSkeleton omega) :=
  L.noPublicTargetTags.2.2

end GaugeBufferedLockedInterface

/-! ## Jointly inhabited toy ledger -/

def toyLedgerHistoryField : FiniteSigmaField Bool where
  Atom := Unit
  atomDecidable := inferInstance
  atom := fun _ => ()

def toyLedgerPivot (_omega : Bool) : Unit :=
  ()

theorem toyLedger_admissibleHistory :
    BalancedBit publicNeutralityToyB ∧
      BalancedConditioning toyLedgerHistoryField publicNeutralityToyB := by
  constructor
  · exact publicNeutralityToy_balanced
  · intro a
    cases a
    simp [toyLedgerHistoryField, publicNeutralityToyB, FiberTrue, FiberFalse]

theorem toyLedger_boundaryMixing :
    BoundaryMixingBound publicNeutralityToyB toyLedgerPivot 0 := by
  intro h
  cases hval : h ()
  · have hcard :
        Fintype.card
          {phi : Bool // (fun w => h (toyLedgerPivot w)) phi =
            publicNeutralityToyB phi} = 1 := by
        simp [toyLedgerPivot, publicNeutralityToyB, hval]
    have hsuccess :
        globalDecoderSuccess (fun w => h (toyLedgerPivot w))
          publicNeutralityToyB = (1 / 2 : Rat) := by
      unfold globalDecoderSuccess
      rw [hcard]
      norm_num
    rw [hsuccess, publicNeutralityToy_balanced]
    norm_num
  · have hcard :
        Fintype.card
          {phi : Bool // (fun w => h (toyLedgerPivot w)) phi =
            publicNeutralityToyB phi} = 1 := by
        simp [toyLedgerPivot, publicNeutralityToyB, hval]
    have hsuccess :
        globalDecoderSuccess (fun w => h (toyLedgerPivot w))
          publicNeutralityToyB = (1 / 2 : Rat) := by
      unfold globalDecoderSuccess
      rw [hcard]
      norm_num
    rw [hsuccess, publicNeutralityToy_balanced]
    norm_num

theorem toyLedger_noPublicTargetTags :
    PairNeutral publicNeutralityToySupport (fun _ : Bool => ()) ∧
      HasMessageOppositePair publicNeutralityToySupport publicNeutralityToyB ∧
        ¬ ∃ f : Unit -> Bool, ∀ omega, publicNeutralityToyB omega = f () := by
  refine ⟨?neutral, publicNeutralityToy_hasOppositePair, ?notSuff⟩
  · intro w0 w1 h
    rfl
  · intro h
    rcases h with ⟨f, hf⟩
    have hfalse := hf false
    have htrue := hf true
    rw [publicNeutralityToyB] at hfalse htrue
    rw [← hfalse] at htrue
    cases htrue

def toyLockedInterface :
    GaugeBufferedLockedInterface
      Bool Bool toyCDENFNeutral toyCDENFSafe toyCDENFGauge Bool Unit Unit Unit
      Unit Unit Unit Bool Unit where
  law := toyV13Law
  target := publicNeutralityToyB
  publicInput := fun omega => omega
  neutralSkeleton := fun _ => ()
  oppositeSupport := publicNeutralityToySupport
  transcript := toyV13Transcript
  observerBit := toyV13Observer
  phaseA := toyV13EvidenceSpineBound
  semantics := toyCDENFSemantics
  observerEvidence := toyObserverEvidenceInterface
  historyField := toyLedgerHistoryField
  pivotSummary := toyLedgerPivot
  epsMix := 0
  safeCost := fun _ => 0
  safeBudget := 0
  gaugeIncidence := fun _ => 0
  gaugeBound := 0
  singleMessage := by
    intro w0 w1 h
    exact h
  hiddenGaugeProduct := by
    intro gamma omega
    cases gamma
    trivial
  noPublicTargetTags := toyLedger_noPublicTargetTags
  atomCompleteness := by
    intro E
    exact CDENF_semantics toyCDENFSemantics E
  gaugeFaithfulness := by
    intro gamma
    cases gamma
    rfl
  safeQSSM := by
    intro q
    norm_num
  boundedGaugeIncidence := by
    intro gamma
    norm_num
  boundaryMixing := toyLedger_boundaryMixing
  admissibleHistories := toyLedger_admissibleHistory

theorem toyLockedInterface_jointly_inhabits_all_nine :
    (∀ w0 w1,
        toyLockedInterface.publicInput w0 = toyLockedInterface.publicInput w1 ->
          toyLockedInterface.target w0 = toyLockedInterface.target w1) ∧
      (∀ gamma omega, toyLockedInterface.semantics.gaugeSat gamma omega) ∧
      (PairNeutral toyLockedInterface.oppositeSupport
          toyLockedInterface.neutralSkeleton ∧
        HasMessageOppositePair toyLockedInterface.oppositeSupport
          toyLockedInterface.target ∧
          ¬ ∃ f : Unit -> Bool,
            ∀ omega, toyLockedInterface.target omega =
              f (toyLockedInterface.neutralSkeleton omega)) ∧
      (∀ E : RawEvidence toyCDENFNeutral toyCDENFSafe toyCDENFGauge,
        toyLockedInterface.semantics.SatNormal (CDENF E) =
          toyLockedInterface.semantics.SatRaw E) ∧
      (∀ gamma : toyCDENFGauge,
        toyLockedInterface.semantics.SatNormal (CDENF (.gauge gamma)) =
          toyLockedInterface.semantics.gaugeSat gamma) ∧
      (∀ q : toyCDENFSafe,
        0 ≤ toyLockedInterface.safeCost q ∧
          toyLockedInterface.safeCost q ≤ toyLockedInterface.safeBudget) ∧
      (∀ gamma : toyCDENFGauge,
        toyLockedInterface.gaugeIncidence gamma ≤ toyLockedInterface.gaugeBound) ∧
      BoundaryMixingBound toyLockedInterface.target toyLockedInterface.pivotSummary
        toyLockedInterface.epsMix ∧
      (BalancedBit toyLockedInterface.target ∧
        BalancedConditioning toyLockedInterface.historyField
          toyLockedInterface.target) := by
  exact
    ⟨toyLockedInterface.singleMessage,
      toyLockedInterface.hiddenGaugeProduct,
      toyLockedInterface.noPublicTargetTags,
      toyLockedInterface.atomCompleteness,
      toyLockedInterface.gaugeFaithfulness,
      toyLockedInterface.safeQSSM,
      toyLockedInterface.boundedGaugeIncidence,
      toyLockedInterface.boundaryMixing,
      toyLockedInterface.admissibleHistories⟩

theorem toyLockedInterface_history_not_target_measurable :
    ¬ MeasurableWrt toyLockedInterface.historyField toyLockedInterface.target :=
  toyLockedInterface.admissible_history_not_target_measurable
    publicNeutralityToy_nontrivial

theorem toyLockedInterface_pivot_not_sufficient :
    ¬ ∃ h0 : Unit -> Bool,
      ∀ omega, toyLockedInterface.target omega =
        h0 (toyLockedInterface.pivotSummary omega) :=
  toyLockedInterface.boundary_mixing_blocks_pivot_sufficiency (by
    change (0 : Rat) < 1 / 2
    norm_num)

end Mettapedia.Computability.PNP
