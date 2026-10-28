import Mettapedia.Computability.PNP.PNPv13EvidenceNormalization
import Mettapedia.Computability.PNP.PNPv13RandomCoinTraceCapture
import Mettapedia.Computability.PNP.PNPv13TraceCaptureImageBudgetObstruction

/-!
# PNP local route coverage: evidence and trace anchors

Evidence-normalization and trace-capture coverage anchors for the local PNP
crux packet.
-/

namespace Mettapedia.Computability.PNP

/-- The v13 evidence-normalization ledger entry is covered only by the exact
residual-atom boundary: safe/gauge normalization is equivalent to absence of a
target-relevant non-neutral atom outside both classes. -/
def V13EvidenceNormalizationCoverage : Prop :=
  ∀ {Atom : Type} (S : V13EvidenceNormalizationSurface Atom),
    S.NormalizesNonNeutral ↔ ¬ S.HasResidualAtom

@[simp] theorem v13EvidenceNormalizationCoverage :
    V13EvidenceNormalizationCoverage := by
  intro Atom S
  exact V13EvidenceNormalizationSurface.normalizesNonNeutral_iff_not_hasResidualAtom S

/-- Route-coverage anchor: a residual atom with positive score blocks both full
safe/gauge normalization and the positive-score weakening. -/
theorem v13EvidenceNormalizationCoverage_anchor_toyResidual_blocks :
    ¬ v13ToyEvidenceSurface.NormalizesNonNeutral ∧
      v13ToyEvidenceSurface.PositiveResidualScore v13ToyEvidenceScore ∧
      ¬ v13ToyEvidenceSurface.PositiveAtomsCovered v13ToyEvidenceScore := by
  exact
    ⟨v13ToyEvidenceSurface_not_normalizesNonNeutral,
      v13ToyEvidenceSurface_positiveResidualScore,
      v13ToyEvidenceSurface_not_positiveAtomsCovered⟩

/-- The v13 trace-capture ledger entry is covered only by the full finite
quotient boundary: deterministic and randomized observers are decodable exactly
when they are constant on target-relevant trace fibers; capturing all Boolean
observers makes the restricted trace map injective; and any finite trace
alphabet or induced Boolean decoder space below the target-relevant support
already blocks universal Boolean capture. -/
def V13TraceCaptureFactorizationCoverage : Prop :=
  (∀ {State Trace Output : Type} [Inhabited Output]
    (S : V13TraceCaptureSurface State Trace) (observer : State → Output),
    S.ObserverTraceDecodable observer ↔
      S.ObserverConstantOnTraceFibers observer) ∧
  (∀ {State Trace Coin Output : Type} [Inhabited Output]
    (S : V13TraceCaptureSurface State Trace)
    (observer : State → Coin → Output),
    S.RandomObserverTraceDecodable observer ↔
      S.RandomObserverConstantOnTraceFibers observer) ∧
  (∀ {State Trace : Type} [DecidableEq State]
    (S : V13TraceCaptureSurface State Trace),
    S.CapturesAllBoolObservers ↔ Function.Injective S.traceOnRelevant) ∧
  (∀ {State Trace : Type} [DecidableEq State]
    (S : V13TraceCaptureSurface State Trace)
    [Fintype (Subtype S.targetRelevant)] [Fintype Trace],
    S.CapturesAllBoolObservers →
      Fintype.card (Subtype S.targetRelevant) ≤ Fintype.card Trace) ∧
  (∀ {State Trace : Type} [DecidableEq State]
    (S : V13TraceCaptureSurface State Trace)
    [Fintype (Subtype S.targetRelevant)] [Fintype Trace],
    Fintype.card Trace < Fintype.card (Subtype S.targetRelevant) →
      ¬ S.CapturesAllBoolObservers) ∧
  (∀ {State Trace : Type} [DecidableEq State]
    (S : V13TraceCaptureSurface State Trace)
    [Fintype (Subtype S.targetRelevant)] [Fintype Trace],
    S.CapturesAllBoolObservers →
      2 ^ Fintype.card (Subtype S.targetRelevant) ≤ 2 ^ Fintype.card Trace) ∧
  ∀ {State Trace : Type} [DecidableEq State]
    (S : V13TraceCaptureSurface State Trace)
    [Fintype (Subtype S.targetRelevant)] [Fintype Trace],
    2 ^ Fintype.card Trace < 2 ^ Fintype.card (Subtype S.targetRelevant) →
      ¬ S.CapturesAllBoolObservers

@[simp] theorem v13TraceCaptureFactorizationCoverage :
    V13TraceCaptureFactorizationCoverage := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro State Trace Output _InhabitedOutput S observer
    exact
      V13TraceCaptureSurface.observerTraceDecodable_iff_constantOnTraceFibers
        S observer
  · intro State Trace Coin Output _InhabitedOutput S observer
    exact
      V13TraceCaptureSurface.randomObserverTraceDecodable_iff_constantOnTraceFibers
        S observer
  · intro State Trace _DecidableEqState S
    exact
      V13TraceCaptureSurface.capturesAllBoolObservers_iff_traceOnRelevant_injective
        S
  · intro State Trace _DecidableEqState S _instRelevant _instTrace hcapture
    exact
      V13TraceCaptureSurface.relevantStateCard_le_traceCard_of_capturesAllBoolObservers
        (S := S) inferInstance inferInstance hcapture
  · intro State Trace _DecidableEqState S _instRelevant _instTrace hcard
    exact
      V13TraceCaptureSurface.not_capturesAllBoolObservers_of_traceCard_lt_relevantStateCard
        (S := S) inferInstance inferInstance hcard
  · intro State Trace _DecidableEqState S _instRelevant _instTrace hcapture
    exact
      V13TraceCaptureSurface.boolClassifierCard_le_traceClassifierCard_of_capturesAllBoolObservers
        (S := S) hcapture
  · intro State Trace _DecidableEqState S _instRelevant _instTrace hcard
    exact
      V13TraceCaptureSurface.not_capturesAllBoolObservers_of_traceClassifierCard_lt
        (S := S) hcard

/-- Route-coverage anchor: a collapsed target-relevant trace fiber with a
Boolean observer conflict blocks both that observer and universal Boolean
observer capture. -/
theorem v13TraceCaptureFactorizationCoverage_anchor_collapsedTrace_blocks :
    ¬ v13CollapsedTraceSurface.ObserverTraceDecodable v13ToyTraceObserver ∧
      v13CollapsedTraceSurface.RelevantTraceCollision ∧
      ¬ v13CollapsedTraceSurface.CapturesAllBoolObservers := by
  exact
    ⟨v13CollapsedTraceSurface_not_observerTraceDecodable,
      v13CollapsedTraceSurface_relevantTraceCollision,
      v13CollapsedTraceSurface_not_capturesAllBoolObservers⟩

/-- Route-coverage anchor: adding a coin parameter does not repair a collapsed
target-relevant trace fiber; one conflicting coin slice still blocks randomized
trace capture. -/
theorem v13TraceCaptureFactorizationCoverage_anchor_collapsedRandomTrace_blocks :
    v13CollapsedTraceSurface.RandomObserverSameTraceConflict
        v13ToyRandomTraceObserver ∧
      ¬ v13CollapsedTraceSurface.RandomObserverTraceDecodable
        v13ToyRandomTraceObserver := by
  exact
    ⟨v13CollapsedTraceSurface_randomSameTraceConflict,
      v13CollapsedTraceSurface_not_randomObserverTraceDecodable⟩

end Mettapedia.Computability.PNP
