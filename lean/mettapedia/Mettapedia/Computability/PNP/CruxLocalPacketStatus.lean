import Mettapedia.Computability.PNP.CruxLedger
import Mettapedia.Computability.PNP.CruxFiniteCoinSubrepairLedger
import Mettapedia.Computability.PNP.CruxLocalRouteCoverageAtomicBudget
import Mettapedia.Computability.PNP.CruxLocalRouteCoverageDecoder
import Mettapedia.Computability.PNP.CruxLocalRouteCoverageEvidenceTrace
import Mettapedia.Computability.PNP.CruxLocalRouteCoverageFielded
import Mettapedia.Computability.PNP.CruxLocalRouteCoverageFiniteEnvelope

/-!
# PNP local packet status

This module assembles the current local PNP crux packet from the route-coverage
propositions, records the exact covered/uncovered repair-class lists, and names
the current next marginal target.
-/

namespace Mettapedia.Computability.PNP

universe u v w z

/-- The current accumulated local PNP packet, as of the deterministic-fiber
conditioning and v13 fixed-field audits. -/
def currentPNPLocalCruxPacket : PNPCruxPacket where
  covers
    | .sameSourceBooleanRecoding => True
    | .sameSourceDeterministicFiber => True
    | .repeatedPositiveFieldedPivot => V13RepeatedPositiveFieldedPivotCoverage
    | .forcedPositiveFieldedStep => V13ForcedPositiveFieldedStepCoverage
    | .fixedFieldBadCell => V13FieldedBadCellCoverage
    | .fieldRefinementOfBadCell => V13FieldRefinementBadCellCoverage
    | .invariantScoreRepair => True
    | .boundedSideChannelRepair => True
    | .shortGlobalDecoderRepair => ShortGlobalDecoderRepairCoverage
    | .cdEvidenceNormalization => V13EvidenceNormalizationCoverage
    | .traceCaptureFactorization => V13TraceCaptureFactorizationCoverage
    | .atomicEvidenceBudget => V13AtomicEvidenceBudgetCoverage
    | .acceiEnvelopeProduct => V13ACCEIEnvelopeProductCoverage.{0}
    | .clockedFiniteUniformKernel => ClockedFiniteUniformKernelCoverage
    | .residualSideInformation => False
    | .randomizedResidual => False
    | .sameSourceFiniteCountApproximation => True
    | .approximateDecorrelation => False
    | .kpolyCompressionBridge => False

/-- Repair classes currently covered by the accumulated local PNP packet. -/
def currentPNPCoveredRepairClasses : List PNPRepairClass :=
  [.sameSourceBooleanRecoding,
    .sameSourceDeterministicFiber,
    .repeatedPositiveFieldedPivot,
    .forcedPositiveFieldedStep,
    .fixedFieldBadCell,
    .fieldRefinementOfBadCell,
    .invariantScoreRepair,
    .boundedSideChannelRepair,
    .shortGlobalDecoderRepair,
    .cdEvidenceNormalization,
    .traceCaptureFactorization,
    .atomicEvidenceBudget,
    .acceiEnvelopeProduct,
    .clockedFiniteUniformKernel,
    .sameSourceFiniteCountApproximation]

/-- Repair classes still outside the accumulated local PNP packet. -/
def currentPNPUncoveredRepairClasses : List PNPRepairClass :=
  [.residualSideInformation,
    .randomizedResidual,
    .approximateDecorrelation,
    .kpolyCompressionBridge]

/-- The covered-class list is exact for the current PNP crux packet. -/
theorem currentPNPCoveredRepairClasses_exact (repair : PNPRepairClass) :
    repair ∈ currentPNPCoveredRepairClasses ↔
      currentPNPLocalCruxPacket.covers repair := by
  cases repair <;> simp [currentPNPCoveredRepairClasses, currentPNPLocalCruxPacket]

/-- The uncovered-class list is exact for the current PNP crux packet. -/
theorem currentPNPUncoveredRepairClasses_exact (repair : PNPRepairClass) :
    repair ∈ currentPNPUncoveredRepairClasses ↔
      ¬ currentPNPLocalCruxPacket.covers repair := by
  cases repair <;> simp [currentPNPUncoveredRepairClasses, currentPNPLocalCruxPacket]

/-- A single honest top-level status theorem for the current packet: the v13
ledger entries are backed by route theorems, while the broad packet is still not
stop-grade because named repair classes remain uncovered. -/
theorem currentPNPLocalCruxPacket_theoremBacked_v13_status :
    currentPNPLocalCruxPacket.covers .repeatedPositiveFieldedPivot ∧
      currentPNPLocalCruxPacket.covers .forcedPositiveFieldedStep ∧
      currentPNPLocalCruxPacket.covers .fixedFieldBadCell ∧
      currentPNPLocalCruxPacket.covers .fieldRefinementOfBadCell ∧
      currentPNPLocalCruxPacket.covers .cdEvidenceNormalization ∧
      currentPNPLocalCruxPacket.covers .traceCaptureFactorization ∧
      currentPNPLocalCruxPacket.covers .atomicEvidenceBudget ∧
      currentPNPLocalCruxPacket.covers .acceiEnvelopeProduct ∧
        ¬ currentPNPLocalCruxPacket.StopGrade := by
  refine
    ⟨v13RepeatedPositiveFieldedPivotCoverage,
      v13ForcedPositiveFieldedStepCoverage,
      v13FieldedBadCellCoverage,
      v13FieldRefinementBadCellCoverage,
      v13EvidenceNormalizationCoverage,
      v13TraceCaptureFactorizationCoverage,
      v13AtomicEvidenceBudgetCoverage,
      v13ACCEIEnvelopeProductCoverage, ?_⟩
  intro hstop
  have hres : currentPNPLocalCruxPacket.covers .residualSideInformation :=
    hstop .residualSideInformation
  simp [currentPNPLocalCruxPacket] at hres

/-- The broad repair classes not closed by the finite-coin stack are exactly the
current synthesis gaps. -/
theorem finiteCoinStackUncoveredBroadRepairClasses_exact
    (repair : PNPRepairClass) :
    repair ∈ finiteCoinStackUncoveredBroadRepairClasses ↔
      repair ∈ currentPNPUncoveredRepairClasses := by
  cases repair <;> simp [finiteCoinStackUncoveredBroadRepairClasses,
    currentPNPUncoveredRepairClasses]

/-- The finite-coin stack contributes to the same-source finite-count branch of
the ledger. -/
theorem finiteCoinStack_under_sameSourceFiniteCountApproximation :
    currentPNPLocalCruxPacket.covers .sameSourceFiniteCountApproximation := by
  simp [currentPNPLocalCruxPacket]

/-- The finite-coin stack does not by itself close broad randomized residual
repairs. -/
theorem finiteCoinStack_does_not_cover_randomizedResidual :
    ¬ currentPNPLocalCruxPacket.covers .randomizedResidual := by
  simp [currentPNPLocalCruxPacket]

/-- The support-sensitive finite-coin randomized-residual subledger does not by
itself close broad randomized residual repairs. -/
theorem randomizedResidualSubrepairStack_does_not_cover_randomizedResidual :
    ¬ currentPNPLocalCruxPacket.covers .randomizedResidual := by
  simp [currentPNPLocalCruxPacket]

/-- The finite-coin stack does not by itself close broad residual side
information repairs. -/
theorem finiteCoinStack_does_not_cover_residualSideInformation :
    ¬ currentPNPLocalCruxPacket.covers .residualSideInformation := by
  simp [currentPNPLocalCruxPacket]

/-- The narrow residual-side-information collision packet does not by itself
close broad residual side-information repairs. -/
theorem residualSideInformationSubrepairStack_does_not_cover_residualSideInformation :
    ¬ currentPNPLocalCruxPacket.covers .residualSideInformation := by
  simp [currentPNPLocalCruxPacket]

/-- The finite-coin stack does not by itself close broad approximate
decorrelation repairs. -/
theorem finiteCoinStack_does_not_cover_approximateDecorrelation :
    ¬ currentPNPLocalCruxPacket.covers .approximateDecorrelation := by
  simp [currentPNPLocalCruxPacket]

/-- The finite-coin stack does not by itself close the manuscript-specific
`Kpoly` compression bridge. -/
theorem finiteCoinStack_does_not_cover_kpolyCompressionBridge :
    ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge := by
  simp [currentPNPLocalCruxPacket]

/-- The narrow `Kpoly` subrepair stack does not by itself close the broad
manuscript-specific `Kpoly` compression bridge. -/
theorem kpolySubrepairStack_does_not_cover_kpolyCompressionBridge :
    ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge := by
  simp [currentPNPLocalCruxPacket]

/-- The current packet covers the v13 evidence-normalization boundary as an
exact residual-atom equivalence. -/
theorem cdEvidenceNormalization_covered_currentPNPLocalCruxPacket :
    currentPNPLocalCruxPacket.covers .cdEvidenceNormalization := by
  exact v13EvidenceNormalizationCoverage

/-- The current packet covers the v13 trace-capture factorization boundary as
an exact trace-fiber constancy equivalence. -/
theorem traceCaptureFactorization_covered_currentPNPLocalCruxPacket :
    currentPNPLocalCruxPacket.covers .traceCaptureFactorization := by
  exact v13TraceCaptureFactorizationCoverage

/-- The current packet covers the v13 atomic-evidence budget boundary at the
full finite exactness surface, including the cancellation obstruction to
equivalence-only repairs. -/
theorem atomicEvidenceBudget_covered_currentPNPLocalCruxPacket :
    currentPNPLocalCruxPacket.covers .atomicEvidenceBudget := by
  exact v13AtomicEvidenceBudgetCoverage

/-- The current packet covers the finite ACCEI/PNLD envelope-product skeleton:
finite Markov pruning plus the sequential one-step rate product bound and its
contrapositive. -/
theorem acceiEnvelopeProduct_covered_currentPNPLocalCruxPacket :
    currentPNPLocalCruxPacket.covers .acceiEnvelopeProduct := by
  exact v13ACCEIEnvelopeProductCoverage

/-- The current packet covers the v13 forced-positive-fielded-step boundary as
an exact finite-count obstruction, not only literal repeated pivots. -/
theorem forcedPositiveFieldedStep_covered_currentPNPLocalCruxPacket :
    currentPNPLocalCruxPacket.covers .forcedPositiveFieldedStep := by
  exact v13ForcedPositiveFieldedStepCoverage

/-- The next highest-marginal target selected by the current ledger.  The
finite-coin stack now has a precise subledger, the postprocessed-side matching
subcase is closed, and the clocked finite-uniform bookkeeping kernel is already
covered.  The next broad gap to push is therefore residual side information:
any useful residual must expose quantified orbit-resolving mass, not merely
exist as an extra retained variable. -/
def currentPNPNextMarginalTarget : PNPRepairClass :=
  .residualSideInformation

/-- The selected next target is still uncovered by the current packet. -/
theorem currentPNPNextMarginalTarget_uncovered :
    ¬ currentPNPLocalCruxPacket.covers currentPNPNextMarginalTarget := by
  simp [currentPNPNextMarginalTarget, currentPNPLocalCruxPacket]

/-- Any packet that still misses the selected next marginal target cannot be
called stop-grade. -/
theorem not_stopGrade_of_not_covers_currentPNPNextMarginalTarget
    {packet : PNPCruxPacket}
    (hmiss : ¬ packet.covers currentPNPNextMarginalTarget) :
    ¬ packet.StopGrade :=
  PNPCruxPacket.not_stopGrade_of_not_covers hmiss

/-- The selected next target is one of the current synthesis gaps. -/
theorem currentPNPNextMarginalTarget_mem_uncovered :
    currentPNPNextMarginalTarget ∈ currentPNPUncoveredRepairClasses := by
  simp [currentPNPNextMarginalTarget, currentPNPUncoveredRepairClasses]

/-- The selected next target is outside the finite-coin subledger. -/
theorem currentPNPNextMarginalTarget_mem_finiteCoin_uncovered_broad :
    currentPNPNextMarginalTarget ∈ finiteCoinStackUncoveredBroadRepairClasses := by
  simp [currentPNPNextMarginalTarget, finiteCoinStackUncoveredBroadRepairClasses]


end Mettapedia.Computability.PNP
