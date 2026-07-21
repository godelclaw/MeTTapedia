import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationCertificate
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationInvariant
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceFiniteQuotient
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitBasis
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignCertificate

/-!
# Genuine Reynolds normalization of the standard trace evaluations

Ordinary matrix trace evaluation is restricted to the independently defined
Reynolds-invariant subspace and transported to signed coinvariants.  The full
`384`-element average is retained.  Thus the checked unsigned `24`-term
matrix evaluates a Reynolds basis vector after division by `24`; no rescaling
of the evaluation functionals is hidden in the conditioning constant.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceEvaluationReynolds

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDCharacterCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16TraceEvaluation
open HypercubicDimension16TraceFiniteQuotient
open HypercubicDimension16TraceOrbitChart
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitBasis
open HypercubicDimension16TraceOrbitHistogramExecutable
open HypercubicDimension16TraceOrbitHistogramSignCertificate
open HypercubicDimension16TraceOrbitExecutableSignature
open HypercubicDimension16TraceOrbitChartSignCertificate
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceEvaluationExecutable
open HypercubicDimension16PhysicalTraceEvaluationData
open HypercubicDimension16PhysicalTraceEvaluationSemantics
open HypercubicDimension16PhysicalTraceEvaluationTraceCertificate
open HypercubicDimension16PhysicalTraceEvaluationInvariant
open HypercubicDimension16PhysicalTraceEvaluationCertificate
open HypercubicDimension16TraceRankCertificateData

/-- Ordinary matrix evaluation restricted to the genuine invariant
subspace. -/
def invariantTraceEvaluation (assignment : Fin 98) :
    sectorFieldOrbitInvariantSubmodule 8 0 →ₗ[ℚ] ℚ :=
  (orbitPlaneTraceEvaluationLinear
      (encodedEvaluationMatrixAt assignment) 8 0).comp
    (sectorFieldOrbitInvariantSubmodule 8 0).subtype

/-- The same functional on the standard signed coinvariant quotient. -/
def coinvariantTraceEvaluation (assignment : Fin 98) :
    FieldEightSignedOrbitCoinvariant →ₗ[ℚ] ℚ :=
  (invariantTraceEvaluation assignment).comp
    fieldEightSignedOrbitCoinvariantEquivInvariant.toLinearMap

/-- The evaluation payload uses exactly the independently certified free
columns from the sparse rank certificate. -/
theorem freeRepresentativeIndex_eq_certifiedFreeColumn
    (index : Fin 98) :
    freeRepresentativeIndex index = certifiedFreeColumn index := by
  have hlookup :
      freeColumn? index.1 =
        some (freeColumns.getD index.1 0) := by
    decide +kernel +revert
  have hcolumn :
      (freeColumnEvidence index).column =
        freeColumns.getD index.1 0 := by
    rw [← Option.some.injEq, ← (freeColumnEvidence index).lookup, hlookup]
  apply Fin.ext
  change (freeColumns.getD index.1 0) % 11654 =
    (freeColumnEvidence index).column
  have hlt : freeColumns.getD index.1 0 < 11654 := by
    rw [← hcolumn]
    exact (freeColumnEvidence index).column_lt
  rw [Nat.mod_eq_of_lt hlt, ← hcolumn]

/-- Reynolds projection of every literal standard trace row is annihilated
by each ordinary traceless matrix assignment. -/
theorem invariantTraceEvaluation_physicalTraceRow_zero
    (assignment : Fin 98) (generator : FieldEightTraceGenerator) :
    invariantTraceEvaluation assignment
        (fieldEightReynoldsToInvariant
          (fieldEightPhysicalTraceRow generator)) = 0 := by
  change orbitPlaneTraceEvaluationLinear
      (encodedEvaluationMatrixAt assignment) 8 0
      (sectorFieldOrbitReynolds 8 0
        (fieldEightPhysicalTraceRow generator)) = 0
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  rw [map_smul, map_sum]
  apply smul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro h _
  rw [fieldEightPhysicalTraceRow_equivariant]
  rw [LinearMap.map_smul]
  rw [fieldEightPhysicalTraceRow_evaluation_zero
    (encodedEvaluationMatrixAt assignment)
    (encodedEvaluationMatrixAt_traceless assignment)]
  simp

theorem labeledPlaneTraceEvaluation_hypercubicAct
    (matrices : PlaneMatrixAssignment ℚ) (h : Hypercubic4)
    (sector : LabeledLocalWordSector 8 0) :
    labeledPlaneTraceEvaluation matrices (sector.hypercubicAct h) =
      labeledPlaneTraceEvaluation
        (fun plane => matrices (planeAction h plane)) sector := by
  rfl

theorem fourPairRepresentativeTraceEvaluationAt_reflection_blind
    (assignment : Fin 98) (index : PositiveRepresentativeIndex)
    (permutation : Fin 24) (reflection : Fin 16) :
    fourPairRepresentativeTraceEvaluationAt assignment index
        (decodedHypercubicCharacterElement permutation reflection) =
      fourPairRepresentativeTraceEvaluationAt assignment index
        (decodedHypercubicCharacterElement permutation 0) := by
  rfl

theorem orbitTraceEvaluation_freeRepresentative_hypercubicAct
    (assignment freeIndex : Fin 98) (h : Hypercubic4) :
    orbitPlaneTraceEvaluation (encodedEvaluationMatrixAt assignment)
        ((positiveRepresentativeTarget
          (freeRepresentativeIndex freeIndex)).hypercubicAct h) =
      fourPairRepresentativeTraceEvaluationAt assignment
        (freeRepresentativeIndex freeIndex) h := by
  rw [positiveRepresentativeTarget,
    FieldRelabelOrbitCarrier.hypercubicAct_mk,
    orbitPlaneTraceEvaluation_mk,
    labeledPlaneTraceEvaluation_hypercubicAct]
  exact (fourPairRepresentativeTraceEvaluationAt_eq_labeled
    freeRepresentatives_have_fourPairTrace assignment freeIndex h).symm

/-- With the genuine Reynolds normalization, the public evaluation matrix is
the checked unsigned matrix divided by `24`. -/
theorem invariantTraceEvaluation_positiveRepresentativeReynoldsVector
    (assignment freeIndex : Fin 98) :
    invariantTraceEvaluation assignment
        (positiveRepresentativeReynoldsVector
          (freeRepresentativeIndex freeIndex)) =
      expectedUnsignedEvaluation assignment freeIndex / 24 := by
  let representative :=
    positiveRepresentativeTarget (freeRepresentativeIndex freeIndex)
  let summand : Hypercubic4 → ℚ := fun h =>
    representative.tensorSign h *
      orbitPlaneTraceEvaluation (encodedEvaluationMatrixAt assignment)
        (representative.hypercubicAct h)
  change orbitPlaneTraceEvaluationLinear
      (encodedEvaluationMatrixAt assignment) 8 0
      (sectorFieldOrbitReynolds 8 0
        (Finsupp.single representative 1)) = _
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  rw [map_smul, map_sum]
  simp only [signedSectorFieldOrbitAction_single,
    orbitPlaneTraceEvaluationLinear_single, one_mul, smul_eq_mul]
  change (1 / 384 : ℚ) * (∑ h : Hypercubic4, summand h) = _
  have hcode :
      (∑ h : Hypercubic4, summand h) =
        ∑ code : Fin 24 × Fin 16,
          summand (decodedHypercubicCharacterElement code.1 code.2) := by
    exact (Equiv.sum_comp hypercubicCharacterCodeEquiv summand).symm
  rw [hcode, Fintype.sum_prod_type]
  have hreflection (permutation : Fin 24) (reflection : Fin 16) :
      summand
          (decodedHypercubicCharacterElement permutation reflection) =
        directRepresentativeTensorSign
            (freeRepresentativeIndex freeIndex)
            (decodedHypercubicCharacterElement permutation 0) *
          fourPairRepresentativeTraceEvaluationAt assignment
            (freeRepresentativeIndex freeIndex)
            (decodedHypercubicCharacterElement permutation 0) := by
    unfold summand representative
    rw [← directRepresentativeTensorSign_eq,
      directRepresentativeTensorSign_character_split,
      representative_reflection_signs_positive, mul_one,
      orbitTraceEvaluation_freeRepresentative_hypercubicAct,
      fourPairRepresentativeTraceEvaluationAt_reflection_blind]
  simp_rw [hreflection]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← Finset.mul_sum]
  change (1 / 384 : ℚ) *
      (16 * fourPairUnsignedReynoldsEvaluation assignment freeIndex) = _
  rw [unsignedEvaluation_replay]
  ring

theorem coinvariantTraceEvaluation_basis
    (assignment freeIndex : Fin 98) :
    coinvariantTraceEvaluation assignment
        (positiveRepresentativeCoinvariantBasis
          (freeRepresentativeIndex freeIndex)) =
      expectedUnsignedEvaluation assignment freeIndex / 24 := by
  simpa [coinvariantTraceEvaluation,
    positiveRepresentativeCoinvariantBasis,
    positiveRepresentativeReynoldsBasis] using
      invariantTraceEvaluation_positiveRepresentativeReynoldsVector
        assignment freeIndex

theorem coinvariantTraceEvaluation_physicalTraceRow_zero
    (assignment : Fin 98) (generator : FieldEightTraceGenerator) :
    coinvariantTraceEvaluation assignment
        (fieldEightCoinvariantTraceRow generator) = 0 := by
  change invariantTraceEvaluation assignment
      (fieldEightReynoldsToInvariant
        (fieldEightPhysicalTraceRow generator)) = 0
  exact invariantTraceEvaluation_physicalTraceRow_zero assignment generator

theorem physicalTraceRelationSubmodule_le_evaluationKernel
    (assignment : Fin 98) :
    fieldEightPhysicalTraceRelationSubmodule ≤
      LinearMap.ker (coinvariantTraceEvaluation assignment) := by
  rw [fieldEightPhysicalTraceRelationSubmodule, Submodule.span_le]
  rintro _ ⟨generator, rfl⟩
  change coinvariantTraceEvaluation assignment
      (fieldEightCoinvariantTraceRow generator) = 0
  exact coinvariantTraceEvaluation_physicalTraceRow_zero assignment generator

/-- The free chart vectors, now viewed in the quotient by every standard
trace row. -/
def physicalTraceFreeClass (index : Fin 98) :
    FieldEightPhysicalTraceQuotient :=
  Submodule.Quotient.mk
    (positiveRepresentativeCoinvariantBasis
      (freeRepresentativeIndex index))

/-- Exact invertibility of the public matrix proves that the `98` free
classes survive independently modulo all standard trace rows. -/
theorem physicalTraceFreeClass_linearIndependent :
    LinearIndependent ℚ physicalTraceFreeClass := by
  rw [Fintype.linearIndependent_iff]
  intro coefficients hsum target
  let value : FieldEightSignedOrbitCoinvariant :=
    ∑ index : Fin 98,
      coefficients index •
        positiveRepresentativeCoinvariantBasis
          (freeRepresentativeIndex index)
  have hmembership : value ∈ fieldEightPhysicalTraceRelationSubmodule := by
    apply (Submodule.Quotient.mk_eq_zero
      fieldEightPhysicalTraceRelationSubmodule).mp
    calc
      Submodule.Quotient.mk value =
          fieldEightPhysicalTraceRelationSubmodule.mkQ value :=
        (Submodule.mkQ_apply
          fieldEightPhysicalTraceRelationSubmodule value).symm
      _ =
          ∑ index : Fin 98,
            coefficients index • physicalTraceFreeClass index := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro index _
        rw [map_smul, Submodule.mkQ_apply]
        rfl
      _ = 0 := hsum
  have hevaluation (assignment : Fin 98) :
      (∑ index : Fin 98,
        expectedUnsignedEvaluation assignment index *
          coefficients index) = 0 := by
    have hzero := LinearMap.mem_ker.mp
      (physicalTraceRelationSubmodule_le_evaluationKernel assignment
        hmembership)
    change coinvariantTraceEvaluation assignment value = 0 at hzero
    simp only [value, map_sum, LinearMap.map_smul,
      coinvariantTraceEvaluation_basis, smul_eq_mul] at hzero
    have hscaled := congrArg (fun scalar : ℚ => 24 * scalar) hzero
    have hscaledZero :
        24 *
            (∑ index : Fin 98,
              coefficients index *
                (expectedUnsignedEvaluation assignment index / 24)) = 0 := by
      simpa using hscaled
    calc
      (∑ index : Fin 98,
          expectedUnsignedEvaluation assignment index *
            coefficients index) =
          24 *
            (∑ index : Fin 98,
              coefficients index *
                (expectedUnsignedEvaluation assignment index / 24)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro index _
        ring
      _ = 0 := hscaledZero
  calc
    coefficients target =
        ∑ column : Fin 98,
          (if target = column then 1 else 0) * coefficients column := by
            simp
    _ = ∑ column : Fin 98,
          (∑ assignment : Fin 98,
            decodedEvaluationInverse target assignment *
              expectedUnsignedEvaluation assignment column) *
            coefficients column := by
          apply Finset.sum_congr rfl
          intro column _
          rw [evaluationInverse_replay]
    _ = ∑ assignment : Fin 98,
          decodedEvaluationInverse target assignment *
            (∑ column : Fin 98,
              expectedUnsignedEvaluation assignment column *
                coefficients column) := by
          calc
            (∑ column : Fin 98,
                (∑ assignment : Fin 98,
                  decodedEvaluationInverse target assignment *
                    expectedUnsignedEvaluation assignment column) *
                  coefficients column) =
                ∑ column : Fin 98, ∑ assignment : Fin 98,
                  (decodedEvaluationInverse target assignment *
                    expectedUnsignedEvaluation assignment column) *
                      coefficients column := by
                  apply Finset.sum_congr rfl
                  intro column _
                  rw [Finset.sum_mul]
            _ = ∑ assignment : Fin 98, ∑ column : Fin 98,
                  (decodedEvaluationInverse target assignment *
                    expectedUnsignedEvaluation assignment column) *
                      coefficients column := Finset.sum_comm
            _ = ∑ assignment : Fin 98,
                  decodedEvaluationInverse target assignment *
                    (∑ column : Fin 98,
                      expectedUnsignedEvaluation assignment column *
                        coefficients column) := by
                  apply Finset.sum_congr rfl
                  intro assignment _
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro column _
                  ring
    _ = 0 := by simp_rw [hevaluation, mul_zero, Finset.sum_const_zero]

end HypercubicDimension16PhysicalTraceEvaluationReynolds
end YangMills
end QuantumTheory
end Mettapedia
