import Mettapedia.QuantumTheory.YangMills.RGBootstrapSlack
import Mettapedia.QuantumTheory.YangMills.SU2CayleyHamiltonTruncationObstruction
import Mettapedia.QuantumTheory.YangMills.WilsonPolymerRecombination

/-!
# Decision ledger for the `SU(2)` coefficient-majorant repair

This module seals the negative branch of the coefficient-majorant pilot on the
exact `SU(2)`, `b = 2` block.  The fixed-boundary Haar integral and its
effective action are genuine block transformations, and union-support
regrouping retains its proved norm-one bound on this block.  However, the
canonical-dimension extraction required between them is not a map on the
evaluated Wilson quotient.  Therefore the same-object recursion constant and
least-depth ledger cannot be formed.

The sixteen-row matrix distinguishes construction/proof from a decisive
obstruction and from work intentionally not reached after that obstruction.
In particular, a downstream row is never marked proved from an assumed
structure field or from a free-syntax analogue.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace SU2MajorantRepairDecision

open SU2WilsonBlockPilot
open SU2CayleyHamiltonTruncationObstruction

/-! ## The actual Haar block map and block-specific recombination -/

/-- The effective block action is definitionally the logarithm of the genuine
fixed-boundary internal-link Haar integral. -/
theorem effectiveBlockAction_is_log_internalHaarIntegral
    (β : ℝ) (V : BoundaryField) :
    effectiveBlockAction β V =
      -Real.log
        (∫ A : InternalField,
          Real.exp (-wilsonAction β (assembleField V A)) ∂volume) := by
  rfl

theorem effectiveBlockAction_zero (V : BoundaryField) :
    effectiveBlockAction 0 V = 0 := by
  rw [effectiveBlockAction, blockPartition_zero]
  simp

/-- Exact union-support regrouping on the plaquette carrier of this block.
This is the mechanical recombination map only; it does not supply the preceding
connected-cumulant/tree-graph estimate. -/
theorem blockPlaquette_unionRecombination_le
    (weight : FinitePolymer BlockPlaquette → ℝ)
    (hweight : ∀ X, 0 ≤ weight X)
    (contribution : FinitePolymerFamily BlockPlaquette → ℝ) :
    polymerActivityMajorant weight (recombineByUnion contribution) ≤
      polymerFamilyMajorant weight contribution :=
  polymerActivityMajorant_recombineByUnion_le weight hweight contribution

/-! ## The requested constant ledger is uninhabited -/

/-- Data fields requested of a completed same-object constant ledger.  No
numbers are inserted unless their factors have been proved for the actual
block map. -/
structure MajorantConstantLedgerData where
  C_fluct : ℝ
  C_cumulant : ℝ
  C_recomb : ℝ
  C_extract : ℝ
  C_basis : ℝ
  C_true : ℝ
  leastEvenDepth : ℕ

/-- Certification obligations for the requested ledger.  The first field is
the already-refuted same-object descent obligation; the remaining fields spell
out the advertised product and least-even-depth arithmetic without assuming
any analytic factor. -/
structure MajorantConstantLedgerCertified
    (L : MajorantConstantLedgerData) : Prop where
  extractionDescends : TraceCanonicalTruncationDescends
  extractionConstant : L.C_extract = 1
  trueConstant :
    L.C_true =
      L.C_fluct * L.C_cumulant * L.C_recomb * L.C_extract * L.C_basis
  depthEven : Even L.leastEvenDepth
  depthCloses : HasTwoSourceBootstrapSlack L.C_true 2 L.leastEvenDepth
  depthLeast :
    ∀ D : ℕ, Even D → HasTwoSourceBootstrapSlack L.C_true 2 D →
      L.leastEvenDepth ≤ D

/-- Existence of a fully certified ledger on the evaluated block quotient. -/
def HasCompletedMajorantConstantLedger : Prop :=
  ∃ L : MajorantConstantLedgerData, MajorantConstantLedgerCertified L

/-- **Constant/depth verdict.**  No requested ledger exists for this pilot,
because every such ledger must contain a descended extraction and that
extraction has been explicitly refuted. -/
theorem no_completedMajorantConstantLedger :
    ¬ HasCompletedMajorantConstantLedger := by
  rintro ⟨L, hL⟩
  exact cayleyHamiltonTruncation_does_not_descend hL.extractionDescends

/-! ## Complete sixteen-row transfer/obstruction matrix -/

/-- The sixteen required fields, in the order of the decision protocol. -/
inductive DecisionField where
  | exactBlockGeometry
  | treeGauge
  | actualWilsonEvaluation
  | offShellRelationsThrough16
  | finiteQuotientBasis
  | canonicalFiltrationCompatibility
  | quotientMajorantNorm
  | descendedExtraction
  | extractionConstant
  | haarFluctuationMap
  | connectedCumulantBound
  | unionSupportRecombination
  | basisConditioning
  | oneStepSameNormBound
  | explicitTrueConstant
  | twoSourceDepthInequality
deriving DecidableEq, Fintype, Repr

/-- Status vocabulary.  `provedOnBlock` is reserved for a theorem or exact
construction on this object. -/
inductive DecisionStatus where
  | provedOnBlock
  | decisiveObstruction
  | relationWitnessSufficientForNegativeBranch
  | notReachedAfterObstruction
deriving DecidableEq, Repr

/-- Machine-readable field status.  Rows one through three, ten, and twelve
are the positive mechanical results.  Row six/eight is the decisive semantic
obstruction.  A complete relation census, quotient basis/norm, and all analytic
rows are not claimed after the negative branch has already terminated. -/
def decisionStatus : DecisionField → DecisionStatus
  | .exactBlockGeometry => .provedOnBlock
  | .treeGauge => .provedOnBlock
  | .actualWilsonEvaluation => .provedOnBlock
  | .offShellRelationsThrough16 => .relationWitnessSufficientForNegativeBranch
  | .finiteQuotientBasis => .notReachedAfterObstruction
  | .canonicalFiltrationCompatibility => .decisiveObstruction
  | .quotientMajorantNorm => .notReachedAfterObstruction
  | .descendedExtraction => .decisiveObstruction
  | .extractionConstant => .notReachedAfterObstruction
  | .haarFluctuationMap => .provedOnBlock
  | .connectedCumulantBound => .notReachedAfterObstruction
  | .unionSupportRecombination => .provedOnBlock
  | .basisConditioning => .notReachedAfterObstruction
  | .oneStepSameNormBound => .notReachedAfterObstruction
  | .explicitTrueConstant => .notReachedAfterObstruction
  | .twoSourceDepthInequality => .notReachedAfterObstruction

/-- Explicit ordered matrix, emitted once for audit and documentation. -/
def decisionMatrix : List (DecisionField × DecisionStatus) :=
  [ (.exactBlockGeometry, .provedOnBlock)
  , (.treeGauge, .provedOnBlock)
  , (.actualWilsonEvaluation, .provedOnBlock)
  , (.offShellRelationsThrough16, .relationWitnessSufficientForNegativeBranch)
  , (.finiteQuotientBasis, .notReachedAfterObstruction)
  , (.canonicalFiltrationCompatibility, .decisiveObstruction)
  , (.quotientMajorantNorm, .notReachedAfterObstruction)
  , (.descendedExtraction, .decisiveObstruction)
  , (.extractionConstant, .notReachedAfterObstruction)
  , (.haarFluctuationMap, .provedOnBlock)
  , (.connectedCumulantBound, .notReachedAfterObstruction)
  , (.unionSupportRecombination, .provedOnBlock)
  , (.basisConditioning, .notReachedAfterObstruction)
  , (.oneStepSameNormBound, .notReachedAfterObstruction)
  , (.explicitTrueConstant, .notReachedAfterObstruction)
  , (.twoSourceDepthInequality, .notReachedAfterObstruction)
  ]

theorem decisionField_count : Fintype.card DecisionField = 16 := by
  decide

theorem decisionMatrix_length : decisionMatrix.length = 16 := by
  rfl

theorem decisionMatrix_agrees_with_status :
    ∀ field : DecisionField,
      (field, decisionStatus field) ∈ decisionMatrix := by
  intro field
  cases field <;> decide

theorem filtrationCompatibility_obstructed :
    ¬ (∀ c : TraceRelationCoefficients,
      TraceSemanticallyEquivalent c 0 →
        TraceSemanticallyEquivalent (traceRelationTruncateThrough16 c) 0) :=
  traceSemanticKernel_not_stable_under_truncation

theorem descendedExtraction_obstructed :
    ¬ TraceCanonicalTruncationDescends :=
  cayleyHamiltonTruncation_does_not_descend

/-- **Machine-checked decision seal.**  It packages only the source theorems
behind the positive and negative rows: exact geometry/tree gauge/evaluation,
the cross-cutoff semantic relation, non-descent, the genuine Haar map, exact
union regrouping, the uninhabited ledger, and matrix exhaustiveness. -/
theorem su2MajorantRepairDecision_sealed :
    Fintype.card BlockVertex = 81 ∧
    Fintype.card InternalLink = 8 ∧
    Fintype.card CoTreeLink = 7 ∧
    (∀ U : BlockLinkField, treeGaugeFix U treeBlockLink = 1) ∧
    TraceSemanticallyEquivalent cayleyHamiltonRelationCoefficients 0 ∧
    (¬ TraceCanonicalTruncationDescends) ∧
    (∀ V : BoundaryField, effectiveBlockAction 0 V = 0) ∧
    (¬ HasCompletedMajorantConstantLedger) ∧
    decisionMatrix.length = 16 := by
  refine ⟨blockVertex_count, internalLink_count, coTreeLink_count,
    treeGaugeFix_treeLink, cayleyHamiltonRelation_semantically_zero,
    cayleyHamiltonTruncation_does_not_descend,
    effectiveBlockAction_zero, no_completedMajorantConstantLedger,
    decisionMatrix_length⟩

end SU2MajorantRepairDecision
end YangMills
end QuantumTheory
end Mettapedia
