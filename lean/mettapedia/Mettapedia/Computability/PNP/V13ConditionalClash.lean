import Mettapedia.Computability.PNP.PNPSteelmanConditional
import Mettapedia.Computability.PNP.V13GaugeBufferedLockedInterface

/-!
# PNP v13 conditional upper/lower clash

This module packages the Phase A-D v13 architecture as a conditional proof
object.  It does not instantiate the concrete ensemble.  The lower side is
derived from a product-small-success/compression-from-success budget machine,
using the same lower-bound chain as `PNPSteelmanConditional`.  The upper side is
isolated as one named self-reduction hypothesis.  The conclusion also carries a
certificate showing that all nine ledger fields were used.
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

/-- Lower-side budget machine: product small-success followed by
compression-from-success.  This is the lower-bound fragment of
`PNPConditionalFramework`, deliberately excluding the final self-reduction
step. -/
structure CompressionLowerFramework where
  Predictor : Type
  short : Predictor -> Prop
  uLocal : Predictor -> Prop
  pivotSuccess : Predictor -> Nat
  tupleSuccess : Predictor -> Nat
  halfBudget : Nat
  halfPlusSlackBudget : Nat
  smallSuccessBudget : Nat
  targetBlocks : Nat
  etaTimes : Nat -> Nat
  kpolyAt : Nat -> Nat
  productSmallSuccess :
    ∀ A : Predictor,
      pivotSuccess A ≤ halfPlusSlackBudget ->
        tupleSuccess A ≤ smallSuccessBudget
  compressionFromSuccess :
    (∀ A : Predictor, short A -> tupleSuccess A ≤ smallSuccessBudget) ->
      etaTimes targetBlocks ≤ kpolyAt targetBlocks

namespace CompressionLowerFramework

/-- Embed the lower-side machine into the existing steelman framework with a
trivial endpoint, so the lower-bound theorem can reuse the checked steelman
chain without hiding any self-reduction content in the lower side. -/
def toSteelmanFramework (F : CompressionLowerFramework) :
    PNPConditionalFramework where
  Predictor := F.Predictor
  short := F.short
  uLocal := F.uLocal
  pivotSuccess := F.pivotSuccess
  tupleSuccess := F.tupleSuccess
  halfBudget := F.halfBudget
  halfPlusSlackBudget := F.halfPlusSlackBudget
  smallSuccessBudget := F.smallSuccessBudget
  targetBlocks := F.targetBlocks
  etaTimes := F.etaTimes
  kpolyAt := F.kpolyAt
  pNeNPClaim := True
  pivotIndependenceStep := F.productSmallSuccess
  compressionFromSuccessStep := F.compressionFromSuccess
  selfReductionClashStep := by
    intro hlower
    trivial

end CompressionLowerFramework

/-- Kernel-flip lower-side input, stated over the self-reduction-free lower
framework. -/
structure CompressionKernelNeutrality (F : CompressionLowerFramework) where
  exactLocalHalfBound :
    ∀ A : F.Predictor, F.uLocal A -> F.pivotSuccess A ≤ F.halfBudget
  halfBudget_le_starBudget :
    F.halfBudget ≤ F.halfPlusSlackBudget

/-- **Retired thin StarSW transfer.** This legacy local-to-short-predictor
implication is retained by the abstract clash plumbing, but it is not Theorem
10.9: it has no size-indexed probability, message scale, exceptional event, or
fixed-clock quantifier.  Manuscript-facing work must use
`V13GlobalMessageIncompressibilityFrontier`. -/
structure CompressionStarSWHardness (F : CompressionLowerFramework) where
  transferLocalNeutralityToShortPredictors :
    (∀ A : F.Predictor, F.uLocal A -> F.pivotSuccess A ≤ F.halfBudget) ->
      ∀ A : F.Predictor, F.short A -> F.pivotSuccess A ≤ F.halfBudget

def CompressionKernelNeutrality.toSteelman
    {F : CompressionLowerFramework}
    (h : CompressionKernelNeutrality F) :
    KernelFlipNeutrality F.toSteelmanFramework where
  exactLocalHalfBound := h.exactLocalHalfBound
  halfBudget_le_starBudget := h.halfBudget_le_starBudget

def CompressionStarSWHardness.toSteelman
    {F : CompressionLowerFramework}
    (h : CompressionStarSWHardness F) :
    StarSWAverageCaseWitnessBitHardness F.toSteelmanFramework where
  transferLocalNeutralityToShortPredictors :=
    h.transferLocalNeutralityToShortPredictors

/-- Lower consequence derived from product small-success and
compression-from-success, via the checked steelman lower-bound chain. -/
theorem compressionLower_of_budget_machine
    {F : CompressionLowerFramework}
    (hKernel : CompressionKernelNeutrality F)
    (hSW : CompressionStarSWHardness F) :
    F.etaTimes F.targetBlocks ≤ F.kpolyAt F.targetBlocks :=
  kpolyLowerBound_of_kernelFlipNeutrality_starSW
    hKernel.toSteelman hSW.toSteelman

/--
The single upper-side open input.

Analytic content carried here: the constant-length self-reduction/P=NP wrapper
forces the same `Kpoly` quantity below the compression floor for the lower-side
budget machine.  No separate lower consequence, upper consequence, or strict
gap field is allowed in `ParameterRecord`.
-/
structure SelfReductionUpperHypothesis (F : CompressionLowerFramework) where
  upperStrictlyBelowCompressionFloor :
    F.kpolyAt F.targetBlocks < F.etaTimes F.targetBlocks

/-- Classification tags for the post-review `ParameterRecord` audit. -/
inductive ParameterFieldStatus where
  | numeric
  | derived
  | openInput
deriving DecidableEq, Repr

/-- One row in the `ParameterRecord` audit. -/
structure ParameterFieldAudit where
  fieldName : String
  status : ParameterFieldStatus
  note : String
deriving Repr

/-- Audit list required by the second-round review: every parameter field is a
number/numeric inequality, a derived finite-budget input, or an explicitly
flagged open analytic input. -/
def v13ParameterRecordAudit : List ParameterFieldAudit := [
  {
    fieldName := "fixedGapBudget",
    status := .numeric,
    note := "Rational bound used to cap the Phase A finite observer gap."
  },
  {
    fieldName := "phaseABudget",
    status := .numeric,
    note := "Numeric inequality converting the derivative-telescoping sum into fixedGapBudget."
  },
  {
    fieldName := "epsSmall",
    status := .numeric,
    note := "Rational boundary-mixing threshold epsMix < 1/2."
  },
  {
    fieldName := "lowerFramework",
    status := .derived,
    note := "Finite product-small-success plus compression-from-success budget machine; it contains no self-reduction step."
  },
  {
    fieldName := "kernelNeutrality",
    status := .derived,
    note := "Finite kernel/local-neutrality half-bound input for the lower-side budget machine."
  },
  {
    fieldName := "starSWHardness",
    status := .openInput,
    note := "Open SW-shaped average-case transfer from local-neutral predictors to all short predictors."
  },
  {
    fieldName := "selfReductionUpper",
    status := .openInput,
    note := "The single upper-side self-reduction/P=NP wrapper hypothesis."
  }
]

theorem v13ParameterRecordAudit_length :
    v13ParameterRecordAudit.length = 7 := by
  rfl

/-- External parameter payload for the conditional clash after the
second-round cleanup.  No conclusion field appears here. -/
structure ParameterRecord
    (L : GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton) where
  fixedGapBudget : Rat
  phaseABudget :
    (1 / 2 : Rat) * L.phaseA.telescoping.derivativeSum ≤ fixedGapBudget
  epsSmall : L.epsMix < (1 / 2 : Rat)
  lowerFramework : CompressionLowerFramework
  kernelNeutrality : CompressionKernelNeutrality lowerFramework
  starSWHardness : CompressionStarSWHardness lowerFramework
  selfReductionUpper : SelfReductionUpperHypothesis lowerFramework

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
  gaugePredicateTotalUsed :
    ∀ gamma omega, L.semantics.gaugeSat gamma omega
  noPublicTargetTagsUsed :
    PairNeutral L.oppositeSupport L.neutralSkeleton ∧
      HasMessageOppositePair L.oppositeSupport L.target ∧
        ¬ ∃ f : Skeleton -> Bool,
          ∀ omega, L.target omega = f (L.neutralSkeleton omega)
  atomCompletenessUsed :
    ∀ E : RawEvidence Neutral Safe Gauge,
      L.semantics.SatNormal (CDENF E) = L.semantics.SatRaw E
  gaugeFaithfulnessUsed :
    ∀ gamma : Gauge,
      L.semantics.SatNormal (CDENF (.gauge gamma)) =
        L.semantics.gaugeSat gamma
  safeQSSMUsed :
    ∀ q : Safe, 0 ≤ L.safeCost q ∧ L.safeCost q ≤ L.safeBudget
  boundedGaugeIncidenceUsed :
    ∀ gamma : Gauge, L.gaugeIncidence gamma ≤ L.gaugeBound
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
    ∀ observer output,
      L.observerEvidence.semantics.SatNormal
          (CDENF
            (L.observerEvidence.observerToEvidence observer output)) =
        fun omega =>
          L.observerEvidence.evalObserver observer
            (L.observerEvidence.publicInput omega) = output
  fieldUse : LedgerFieldUseCertificate L P
  lowerConsequence :
    P.lowerFramework.etaTimes P.lowerFramework.targetBlocks ≤
      P.lowerFramework.kpolyAt P.lowerFramework.targetBlocks
  selfReductionUpper :
    P.lowerFramework.kpolyAt P.lowerFramework.targetBlocks <
      P.lowerFramework.etaTimes P.lowerFramework.targetBlocks
  noConsistentBounds : False

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
      lowerConsequence :=
        compressionLower_of_budget_machine
          P.kernelNeutrality P.starSWHardness
      selfReductionUpper :=
        P.selfReductionUpper.upperStrictlyBelowCompressionFloor
      noConsistentBounds := ?noConsistentBounds }
  · exact le_trans (phaseA_gap_le_half_derivative_sum L.phaseA) P.phaseABudget
  · intro observer output
    exact observerToCDENF_sat L.observerEvidence observer output
  · exact
      { singleMessageUsed := L.singleMessage
        samePublicNotOpposite :=
          sameFullY_noOpposite L.publicInput L.target L.singleMessage
        gaugePredicateTotalUsed := L.gaugePredicateTotal
        noPublicTargetTagsUsed := L.noPublicTargetTags
        atomCompletenessUsed := L.atomCompleteness
        gaugeFaithfulnessUsed := L.gaugeFaithfulness
        safeQSSMUsed := L.safeQSSM
        boundedGaugeIncidenceUsed := L.boundedGaugeIncidence
        boundaryMixingUsed := L.boundaryMixing
        admissibleHistoriesUsed := L.admissibleHistories
        historyNotTargetMeasurable :=
          L.admissible_history_not_target_measurable (by
            rcases L.noPublicTargetTags.2.1 with ⟨w0, w1, _hs, h0, h1⟩
            exact ⟨w1, w0, h1, h0⟩)
        pivotNotSufficient :=
          L.boundary_mixing_blocks_pivot_sufficiency P.epsSmall
        neutralSkeletonNotSufficient :=
          L.neutral_skeleton_not_target_sufficient }
  · exact
      not_lt_of_ge
        (compressionLower_of_budget_machine
          P.kernelNeutrality P.starSWHardness)
        P.selfReductionUpper.upperStrictlyBelowCompressionFloor

/-- The toy ledger supports the same Phase-D conditional theorem.  No concrete
ensemble parameters are constructed here. -/
theorem toyLockedInterface_conditional_clash
    (P : ParameterRecord toyLockedInterface) :
    UpperLowerClash toyLockedInterface P :=
  v13_upperLowerClash toyLockedInterface P

end Mettapedia.Computability.PNP
