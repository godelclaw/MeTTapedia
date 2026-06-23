import Mettapedia.Computability.PNP.CruxKpolyPromotedPacket
import Mettapedia.Computability.PNP.CruxKpolyActualLocalExactZAB

/-!
# PNP crux current Kpoly bridge status

This module is the live status surface for the decomposed PNP crux ledger.  It
states which current packet entries are covered, which named gaps remain, and
the strongest honest status available without adding an artificial
gap-completed packet.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- A packet extending the current local packet is stop-grade exactly when it
covers every currently named gap. -/
theorem stopGrade_iff_covers_currentPNP_gaps_of_extends_current
    {packet : PNPCruxPacket}
    (hExtends : packet.Extends currentPNPLocalCruxPacket) :
    packet.StopGrade ↔ packet.CoversList currentPNPUncoveredRepairClasses := by
  constructor
  · intro hstop repair _
    exact hstop repair
  · intro hGaps repair
    by_cases hCurrent : currentPNPLocalCruxPacket.covers repair
    · exact hExtends repair hCurrent
    · exact hGaps repair ((currentPNPUncoveredRepairClasses_exact repair).2 hCurrent)

/-- An extension of the current packet is not stop-grade if it still fails to
cover the current gap list. -/
theorem not_stopGrade_of_not_covers_currentPNP_gaps_of_extends_current
    {packet : PNPCruxPacket}
    (hExtends : packet.Extends currentPNPLocalCruxPacket)
    (hNotGaps : ¬ packet.CoversList currentPNPUncoveredRepairClasses) :
    ¬ packet.StopGrade := by
  intro hstop
  exact hNotGaps
    ((stopGrade_iff_covers_currentPNP_gaps_of_extends_current hExtends).1 hstop)

/-- The current packet still leaves residual-side-information repairs outside
the formal block. -/
theorem residualSideInformation_uncovered_currentPNPLocalCruxPacket :
    ¬ currentPNPLocalCruxPacket.covers .residualSideInformation := by
  simp [currentPNPLocalCruxPacket]

/-- The current accumulated local PNP packet is not stop-grade: residual side
information remains a named live repair class outside the formal block. -/
theorem not_stopGrade_currentPNPLocalCruxPacket :
    ¬ currentPNPLocalCruxPacket.StopGrade := by
  intro hstop
  exact residualSideInformation_uncovered_currentPNPLocalCruxPacket
    (hstop .residualSideInformation)

/-- The current packet also leaves randomized residual repairs outside the
formal block. -/
theorem randomizedResidual_uncovered_currentPNPLocalCruxPacket :
    ¬ currentPNPLocalCruxPacket.covers .randomizedResidual := by
  simp [currentPNPLocalCruxPacket]

/-- The current packet covers the finite-count same-source approximation
subcase supplied by `ApproximateDecorrelationObstruction.lean`.  This is not a
claim that broad approximate-decorrelation repairs are closed. -/
theorem sameSourceFiniteCountApproximation_covered_currentPNPLocalCruxPacket :
    currentPNPLocalCruxPacket.covers .sameSourceFiniteCountApproximation := by
  simp [currentPNPLocalCruxPacket]

/-- The current packet leaves approximate-decorrelation repairs outside the
formal block. -/
theorem approximateDecorrelation_uncovered_currentPNPLocalCruxPacket :
    ¬ currentPNPLocalCruxPacket.covers .approximateDecorrelation := by
  simp [currentPNPLocalCruxPacket]

/-- The current packet leaves the final `Kpoly` compression bridge outside the
formal block. -/
theorem kpolyCompressionBridge_uncovered_currentPNPLocalCruxPacket :
    ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge := by
  simp [currentPNPLocalCruxPacket]

/-- The current packet now includes the abstract finite counting kernel for the
clocked `Kpoly` bridge. -/
theorem clockedFiniteUniformKernel_covered_currentPNPLocalCruxPacket :
    currentPNPLocalCruxPacket.covers .clockedFiniteUniformKernel := by
  exact clockedFiniteUniformKernelCoverage

/-- Current strongest honest synthesis status: the v13 route entries now have
theorem-backed ledger coverage, the abstract clocked finite-uniform kernel is
covered, the concrete bit-vector exact ZAB ERM family closes the clocked
payload at its explicit budget, and the bare exact-visible interface is still
insufficient.  The broad manuscript-specific `Kpoly` bridge remains uncovered,
so the current packet is not stop-grade. -/
theorem currentPNPStrongestHonestStatus :
    currentPNPLocalCruxPacket.covers .repeatedPositiveFieldedPivot ∧
      currentPNPLocalCruxPacket.covers .forcedPositiveFieldedStep ∧
      currentPNPLocalCruxPacket.covers .fixedFieldBadCell ∧
      currentPNPLocalCruxPacket.covers .fieldRefinementOfBadCell ∧
      currentPNPLocalCruxPacket.covers .cdEvidenceNormalization ∧
      currentPNPLocalCruxPacket.covers .traceCaptureFactorization ∧
      currentPNPLocalCruxPacket.covers .atomicEvidenceBudget ∧
      currentPNPLocalCruxPacket.covers .acceiEnvelopeProduct ∧
      currentPNPLocalCruxPacket.covers .clockedFiniteUniformKernel ∧
      (∀ {r k clock : ℕ} {Index : Type u} [Fintype (BitVec r)]
        (samples :
          Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool),
        ClockedKpolyFiniteLearningPayload
          (bitVecZABDecisionListERMFamily
            (r := r) (k := k) (Index := Index) samples)
          (r + 2 * k + 1) clock) ∧
      (∀ {Z : Type v} [Fintype Z] {k s clock : ℕ}
        (_ : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)),
        ¬ (∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
          ClockedKpolyFiniteLearningPayload G s clock)) ∧
      ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge ∧
      ¬ currentPNPLocalCruxPacket.StopGrade := by
  refine
    ⟨v13RepeatedPositiveFieldedPivotCoverage,
      v13ForcedPositiveFieldedStepCoverage,
      v13FieldedBadCellCoverage,
      v13FieldRefinementBadCellCoverage,
      v13EvidenceNormalizationCoverage,
      v13TraceCaptureFactorizationCoverage,
      v13AtomicEvidenceBudgetCoverage,
      v13ACCEIEnvelopeProductCoverage,
      clockedFiniteUniformKernelCoverage, ?_, ?_,
      kpolyCompressionBridge_uncovered_currentPNPLocalCruxPacket,
      not_stopGrade_currentPNPLocalCruxPacket⟩
  · intro r k clock Index _FintypeBitVec samples
    exact
      bitVecZABDecisionListERMClockedKpolyFiniteLearningPayload
        (r := r) (k := k) (clock := clock) (Index := Index) samples
  · intro Z _FintypeZ k s clock hs
    exact
      currentExactVisibleInterface_not_forall_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
        (Z := Z) (k := k) (s := s) (clock := clock) hs

end Mettapedia.Computability.PNP
