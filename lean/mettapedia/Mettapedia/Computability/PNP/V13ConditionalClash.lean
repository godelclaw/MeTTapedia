import Mettapedia.Computability.PNP.V13GaugeBufferedLockedInterface

/-!
# PNP v13 conditional upper/lower clash

This module packages the Phase A-D v13 architecture as a conditional proof
object.  It does not instantiate the concrete ensemble.  Instead, an external
`ParameterRecord` supplies the lower/upper numeric consequences, and the main
theorem turns a gauge-buffered locked ledger plus those parameters into an
explicit clash record.  The record also carries a certificate showing that all
nine ledger fields were used.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u v w x y z a b c d e f

variable {Omega : Type u} [Fintype Omega] [Nonempty Omega]
variable {Public : Type v} {Neutral : Type w} {Safe : Type x}
variable {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
variable {Pair : Type a} [Fintype Pair] {Stage : Type b} {Branch : Type c}
variable {HistoryAtom : Type d} {Pivot : Type e}
variable {Observer : Type f} {Output : Type f} {Skeleton : Type w}

/-- External parameter payload for the conditional clash.  These are the
non-Phase-E inputs: a derivative-to-gap budget, small boundary-mixing error,
nondegeneracy, probes for the safe/gauge/observer ledgers, and the abstract
lower/upper bounds whose simultaneous satisfaction is the clash. -/
structure ParameterRecord
    (L : GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton) where
  fixedGapBudget : Rat
  phaseABudget :
    (1 / 2 : Rat) * L.phaseA.telescoping.derivativeSum ≤ fixedGapBudget
  epsSmall : L.epsMix < (1 / 2 : Rat)
  targetNondegenerate : NontrivialWitnessBit L.target
  safeProbe : Safe
  gaugeProbe : Gauge
  observerProbe : Observer
  outputProbe : Output
  evidenceProbe : RawEvidence Neutral Safe Gauge
  lowerBound : Rat
  upperBound : Rat
  witnessBound : Rat
  compressionLower : lowerBound ≤ witnessBound
  selfReductionUpper : witnessBound ≤ upperBound
  upper_lt_lower : upperBound < lowerBound

/-- Evidence that Phase D used every one of the nine ledger fields. -/
structure LedgerFieldUseCertificate
    (L : GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (P : ParameterRecord L) where
  singleMessageUsed :
    ∀ w0 w1, L.publicInput w0 = L.publicInput w1 ->
      L.target w0 = L.target w1
  samePublicNotOpposite :
    ¬ ∃ w0 w1,
      L.publicInput w0 = L.publicInput w1 ∧
        L.target w0 = false ∧ L.target w1 = true
  hiddenGaugeProductUsed :
    ∀ omega, L.semantics.gaugeSat P.gaugeProbe omega
  noPublicTargetTagsUsed :
    PairNeutral L.oppositeSupport L.neutralSkeleton ∧
      HasMessageOppositePair L.oppositeSupport L.target ∧
        ¬ ∃ f : Skeleton -> Bool,
          ∀ omega, L.target omega = f (L.neutralSkeleton omega)
  atomCompletenessUsed :
    L.semantics.SatNormal (CDENF P.evidenceProbe) =
      L.semantics.SatRaw P.evidenceProbe
  gaugeFaithfulnessUsed :
    L.semantics.SatNormal (CDENF (.gauge P.gaugeProbe)) =
      L.semantics.gaugeSat P.gaugeProbe
  safeQSSMUsed :
    0 ≤ L.safeCost P.safeProbe ∧
      L.safeCost P.safeProbe ≤ L.safeBudget
  boundedGaugeIncidenceUsed :
    L.gaugeIncidence P.gaugeProbe ≤ L.gaugeBound
  boundaryMixingUsed :
    BoundaryMixingBound L.target L.pivotSummary L.epsMix
  admissibleHistoriesUsed :
    BalancedBit L.target ∧
      BalancedConditioning L.historyField L.target
  historyNotTargetMeasurable :
    ¬ MeasurableWrt L.historyField L.target
  pivotNotSufficient :
    ¬ ∃ h0 : Pivot -> Bool,
      ∀ omega, L.target omega = h0 (L.pivotSummary omega)
  neutralSkeletonNotSufficient :
    ¬ ∃ f : Skeleton -> Bool,
      ∀ omega, L.target omega = f (L.neutralSkeleton omega)

/-- The Phase D conclusion: the finite Phase-A observer gap is below the
declared fixed budget, observer outputs are expanded through CD-ENF, all nine
ledger fields have been consumed, and the supplied lower/upper consequences
form an incompatible interval. -/
structure UpperLowerClash
    (L : GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (P : ParameterRecord L) where
  phaseAGapBound :
    Gap L.law L.target L.transcript L.observerBit ≤ P.fixedGapBudget
  observerNormalized :
    L.observerEvidence.semantics.SatNormal
        (CDENF
          (L.observerEvidence.observerToEvidence
            P.observerProbe P.outputProbe)) =
      fun omega =>
        L.observerEvidence.evalObserver P.observerProbe
          (L.observerEvidence.publicInput omega) = P.outputProbe
  fieldUse : LedgerFieldUseCertificate L P
  lowerConsequence : P.lowerBound ≤ P.witnessBound
  upperConsequence : P.witnessBound ≤ P.upperBound
  upperBelowLower : P.upperBound < P.lowerBound
  noConsistentInterval :
    ¬ (P.lowerBound ≤ P.witnessBound ∧ P.witnessBound ≤ P.upperBound)

/-- Phase D: a gauge-buffered locked ledger plus the external parameter record
produces the conditional upper/lower clash. -/
theorem v13_upperLowerClash
    (L : GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (P : ParameterRecord L) :
    UpperLowerClash L P := by
  refine
    { phaseAGapBound := ?phaseAGapBound
      observerNormalized := ?observerNormalized
      fieldUse := ?fieldUse
      lowerConsequence := P.compressionLower
      upperConsequence := P.selfReductionUpper
      upperBelowLower := P.upper_lt_lower
      noConsistentInterval := ?noConsistentInterval }
  · exact le_trans (phaseA_gap_le_half_derivative_sum L.phaseA) P.phaseABudget
  · exact
      observerToCDENF_sat
        L.observerEvidence P.observerProbe P.outputProbe
  · exact
      { singleMessageUsed := L.singleMessage
        samePublicNotOpposite :=
          sameFullY_noOpposite L.publicInput L.target L.singleMessage
        hiddenGaugeProductUsed := by
          intro omega
          exact L.hiddenGaugeProduct P.gaugeProbe omega
        noPublicTargetTagsUsed := L.noPublicTargetTags
        atomCompletenessUsed := L.atomCompleteness P.evidenceProbe
        gaugeFaithfulnessUsed := L.gaugeFaithfulness P.gaugeProbe
        safeQSSMUsed := L.safeQSSM P.safeProbe
        boundedGaugeIncidenceUsed := L.boundedGaugeIncidence P.gaugeProbe
        boundaryMixingUsed := L.boundaryMixing
        admissibleHistoriesUsed := L.admissibleHistories
        historyNotTargetMeasurable :=
          L.admissible_history_not_target_measurable P.targetNondegenerate
        pivotNotSufficient :=
          L.boundary_mixing_blocks_pivot_sufficiency P.epsSmall
        neutralSkeletonNotSufficient :=
          L.neutral_skeleton_not_target_sufficient }
  · intro h
    linarith [h.1, h.2, P.upper_lt_lower]

/-- The toy ledger supports the same Phase-D conditional theorem.  No concrete
ensemble parameters are constructed here. -/
theorem toyLockedInterface_conditional_clash
    (P : ParameterRecord toyLockedInterface) :
    UpperLowerClash toyLockedInterface P :=
  v13_upperLowerClash toyLockedInterface P

end Mettapedia.Computability.PNP
