import Mettapedia.Computability.PNP.CruxKpolyBridgeCurrentStatus
import Mettapedia.Computability.PNP.CruxKpolyCanonicalZABERMRouteCoverage

/-!
# Regression checks for V13 route coverage in the PNP crux packet

Canonical ZAB ERM and V13 route-coverage wrappers extracted from the historical
packet-status regression module.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
open scoped ENNReal

universe u v w z

theorem canonical_zab_erm_route_coverage_regression :
    CanonicalZABERMRouteCoverage := by
  exact canonicalZABERMRouteCoverage

theorem canonical_zab_erm_route_clocked_payload_and_strict_budget_regression
    {Z : Type v} [Fintype Z] {r k clock : ℕ} {Index : Type u}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index} {q : ℝ≥0∞}
    (h :
  CanonicalZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ClockedKpolyFiniteLearningPayload G (r + 2 * k + 1) clock ∧
      (r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k) →
        ¬ Function.Surjective G.predict) := by
  rcases
      canonicalZABERMRouteCoverage
        (Z := Z) (r := r) (k := k) (clock := clock) (Index := Index)
        (μ := μ) (zfeat := zfeat) (G := G) (q := q) h
    with
    ⟨_, _, _, _, hpayload, hstrict⟩
  exact ⟨hpayload, hstrict⟩

theorem current_pnp_packet_v13_repeated_positive_fielded_pivot_covered_regression :
    currentPNPLocalCruxPacket.covers .repeatedPositiveFieldedPivot := by
  exact v13RepeatedPositiveFieldedPivotCoverage

theorem current_pnp_packet_v13_forced_positive_fielded_step_covered_regression :
    currentPNPLocalCruxPacket.covers .forcedPositiveFieldedStep := by
  exact forcedPositiveFieldedStep_covered_currentPNPLocalCruxPacket

theorem v13_forced_positive_fielded_step_bool_pair_forced_diagonal_blocks_regression :
    V13FieldSwitchingInstantiated
      [v13BoolPairUnitFieldedStep,
        v13BoolPairSecondCoordinateUnitFieldedStep] ∧
      ¬ V13FieldSwitchingInstantiated
        [v13BoolPairUnitFieldedStep,
          v13BoolPairSecondCoordinateUnitFieldedStep,
          v13BoolPairDiagonalUnitFieldedStep] := by
  exact v13BoolPairFirstSecondThenForcedDiagonal_blocked

theorem current_pnp_packet_v13_fixed_field_bad_cell_covered_regression :
    currentPNPLocalCruxPacket.covers .fixedFieldBadCell := by
  exact v13FieldedBadCellCoverage

theorem current_pnp_packet_v13_field_refinement_bad_cell_covered_regression :
    currentPNPLocalCruxPacket.covers .fieldRefinementOfBadCell := by
  exact v13FieldRefinementBadCellCoverage

theorem current_pnp_packet_v13_cd_evidence_normalization_covered_regression :
    currentPNPLocalCruxPacket.covers .cdEvidenceNormalization := by
  exact cdEvidenceNormalization_covered_currentPNPLocalCruxPacket

theorem v13_evidence_normalization_toy_residual_blocks_regression :
    ¬ v13ToyEvidenceSurface.NormalizesNonNeutral ∧
      v13ToyEvidenceSurface.PositiveResidualScore v13ToyEvidenceScore ∧
      ¬ v13ToyEvidenceSurface.PositiveAtomsCovered v13ToyEvidenceScore := by
  exact v13EvidenceNormalizationCoverage_anchor_toyResidual_blocks

theorem current_pnp_packet_v13_trace_capture_factorization_covered_regression :
    currentPNPLocalCruxPacket.covers .traceCaptureFactorization := by
  exact traceCaptureFactorization_covered_currentPNPLocalCruxPacket

instance : Fintype V13ToyTraceState where
  elems := {.left, .right}
  complete := by
    intro s
    cases s <;> simp

noncomputable instance : Fintype (Subtype v13CollapsedTraceSurface.targetRelevant) :=
  Fintype.ofEquiv V13ToyTraceState
    (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm

theorem v13_trace_capture_collapsed_trace_blocks_regression :
    ¬ v13CollapsedTraceSurface.ObserverTraceDecodable v13ToyTraceObserver ∧
      v13CollapsedTraceSurface.RelevantTraceCollision ∧
      ¬ v13CollapsedTraceSurface.CapturesAllBoolObservers := by
  exact v13TraceCaptureFactorizationCoverage_anchor_collapsedTrace_blocks

theorem v13_trace_capture_collapsed_random_trace_blocks_regression :
    v13CollapsedTraceSurface.RandomObserverSameTraceConflict
        v13ToyRandomTraceObserver ∧
      ¬ v13CollapsedTraceSurface.RandomObserverTraceDecodable
        v13ToyRandomTraceObserver := by
  exact v13TraceCaptureFactorizationCoverage_anchor_collapsedRandomTrace_blocks

theorem v13_trace_capture_collapsed_trace_cardinality_budget_regression :
    (Fintype.card Unit <
        Fintype.card (Subtype v13CollapsedTraceSurface.targetRelevant)) ∧
      ¬ v13CollapsedTraceSurface.CapturesAllBoolObservers := by
  have hcard :
      Fintype.card (Subtype v13CollapsedTraceSurface.targetRelevant) =
        Fintype.card V13ToyTraceState := by
    exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  refine ⟨?_, ?_⟩
  · rw [hcard]
    decide
  · rcases
      (traceCaptureFactorization_covered_currentPNPLocalCruxPacket :
        V13TraceCaptureFactorizationCoverage) with
      ⟨_, _, _, _, hsmallTrace, _, _⟩
    exact
      hsmallTrace v13CollapsedTraceSurface
        (by
          rw [hcard]
          decide)

theorem v13_trace_capture_collapsed_trace_image_budget_regression :
    (2 ^ Fintype.card Unit <
        2 ^ Fintype.card (Subtype v13CollapsedTraceSurface.targetRelevant)) ∧
      ¬ v13CollapsedTraceSurface.CapturesAllBoolObservers := by
  have hcard :
      Fintype.card (Subtype v13CollapsedTraceSurface.targetRelevant) =
        Fintype.card V13ToyTraceState := by
    exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  refine ⟨?_, ?_⟩
  · rw [hcard]
    decide
  · rcases
      (traceCaptureFactorization_covered_currentPNPLocalCruxPacket :
        V13TraceCaptureFactorizationCoverage) with
      ⟨_, _, _, _, _, _, hsmallImage⟩
    exact
      hsmallImage v13CollapsedTraceSurface
        (by
          rw [hcard]
          decide)

theorem current_pnp_packet_v13_atomic_evidence_budget_covered_regression :
    currentPNPLocalCruxPacket.covers .atomicEvidenceBudget := by
  exact atomicEvidenceBudget_covered_currentPNPLocalCruxPacket

theorem v13_atomic_evidence_budget_double_counted_atom_blocks_regression :
    v13DoubleCountedBudgetSurface.atomBudget = 1 ∧
      v13DoubleCountedBudgetSurface.coordinateSummedCost = 2 ∧
      ¬ v13DoubleCountedBudgetSurface.NoDoubleCounting ∧
      v13DoubleCountedBudgetSurface.atomBudget <
        v13DoubleCountedBudgetSurface.coordinateSummedCost := by
  exact v13AtomicEvidenceBudgetCoverage_anchor_doubleCountedAtom_blocks

theorem v13_atomic_evidence_budget_cancellation_blocks_regression :
    v13CancellationBudgetSurface.coordinateSummedCost =
        v13CancellationBudgetSurface.atomBudget ∧
      (v13CancellationBudgetSurface.NoDoubleCounting ↔
        v13CancellationBudgetSurface.AllPositiveCostAtomsCharged) ∧
      ¬ v13CancellationBudgetSurface.ExactnessSideConditions := by
  exact v13AtomicEvidenceBudgetCoverage_anchor_cancellation_blocks

theorem
    current_pnp_packet_v13_atomic_evidence_budget_equivalence_only_not_enough_regression :
    ¬ ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
        (S : V13AtomicEvidenceBudgetSurface Coord Atom) [DecidableRel S.charges],
        S.coordinateSummedCost = S.atomBudget →
          (S.NoDoubleCounting ↔ S.AllPositiveCostAtomsCharged) →
          S.ExactnessSideConditions := by
  have hcover : V13AtomicEvidenceBudgetCoverage :=
    atomicEvidenceBudget_covered_currentPNPLocalCruxPacket
  exact hcover.2.2

theorem current_pnp_packet_v13_accei_envelope_product_covered_regression :
    currentPNPLocalCruxPacket.covers .acceiEnvelopeProduct := by
  exact acceiEnvelopeProduct_covered_currentPNPLocalCruxPacket

theorem v13_accei_envelope_product_good_pruning_coverage_regression
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ)
    (hbudget : (∑ i, η i) ≤ budget) :
    Fintype.card ι - budget / (threshold + 1) ≤
        acceiGoodCount ι η threshold ∧
      (budget / (threshold + 1) < Fintype.card ι →
        ∃ i : ι, η i ≤ threshold) := by
  exact
    ⟨v13ACCEIEnvelopeProductCoverage.{u}.2.1 η threshold budget hbudget,
      v13ACCEIEnvelopeProductCoverage.{u}.2.2.1
        η threshold budget hbudget⟩

theorem v13_accei_envelope_product_markov_sharpness_coverage_regression
    (threshold : ℕ) :
    acceiBadCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold *
        (threshold + 1) =
        ∑ b : Bool, oneGoodOneBadACCEIEnvelope threshold b ∧
      Fintype.card Bool - (threshold + 1) / (threshold + 1) =
          acceiGoodCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold ∧
        ¬ ∀ b : Bool, oneGoodOneBadACCEIEnvelope threshold b ≤ threshold := by
  exact
    ⟨v13ACCEIEnvelopeProductCoverage.{0}.2.2.2.1 threshold,
      v13ACCEIEnvelopeProductCoverage.{0}.2.2.2.2.1 threshold⟩

end Mettapedia.Computability.PNP.CruxSynthesisRegression
