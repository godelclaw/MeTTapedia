import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationData
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitExecutableSignature

/-!
# Transparent matrix evaluations for the 98 free trace classes

The evaluator follows the stored trace permutation cycle by cycle and uses
ordinary `2 x 2` matrix multiplication.  It sums the signed evaluations over
the 24 standard unsigned coordinate permutations.  The reflection factor in
the full Reynolds average is handled semantically after the finite replay.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceEvaluationExecutable

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open SU2LatticeFDCensusNoGo
open HypercubicRawFDCharacterCensus
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitExecutableSignature
open HypercubicDimension16PhysicalTraceEvaluationData

@[reducible] def encodedMatrix (code : Array Int) :
    Matrix (Fin 2) (Fin 2) ℚ :=
  fun row column => (code.getD (2 * row.1 + column.1) 0 : ℚ)

@[reducible] def encodedEvaluationMatrixAt
    (assignment : Fin 98) (plane : OrientedPlane) :
    Matrix (Fin 2) (Fin 2) ℚ :=
  let assignmentCode := evaluationAssignments.getD assignment.1 #[]
  let libraryIndex := assignmentCode.getD plane.1 0
  encodedMatrix (matrixLibrary.getD libraryIndex #[])

@[reducible] def encodedTraceCycleLength
    (code : Array Nat) (root : Fin 8) : Nat :=
  if encodedTraceIterate8 code 1 root = root then 1
  else if encodedTraceIterate8 code 2 root = root then 2
  else if encodedTraceIterate8 code 3 root = root then 3
  else if encodedTraceIterate8 code 4 root = root then 4
  else if encodedTraceIterate8 code 5 root = root then 5
  else if encodedTraceIterate8 code 6 root = root then 6
  else if encodedTraceIterate8 code 7 root = root then 7
  else 8

@[reducible] def encodedTraceWordProduct
    (assignment : Fin 98) (code : Array Nat) (h : Hypercubic4)
    (root : Fin 8) : Nat → Matrix (Fin 2) (Fin 2) ℚ
  | 0 => 1
  | length + 1 =>
      encodedTraceWordProduct assignment code h root length *
        encodedEvaluationMatrixAt assignment
          (planeAction h
            (encodedPlane code (encodedTraceIterate8 code length root)))

@[reducible] def encodedTraceRootMinimal
    (code : Array Nat) (root : Fin 8) : Prop :=
  ∀ offset : Fin 8, root ≤ encodedTraceIterate8 code offset.1 root

/-- Ordinary product-of-traces evaluation of a checked representative after
one unsigned coordinate action. -/
@[reducible] def directRepresentativeTraceEvaluationAt
    (assignment : Fin 98) (index : PositiveRepresentativeIndex)
    (h : Hypercubic4) : ℚ :=
  let code := positiveRepresentativeCode index
  ∏ root : Fin 8,
    if encodedTraceRootMinimal code root then
      Matrix.trace
        (encodedTraceWordProduct assignment code h root
          (encodedTraceCycleLength code root))
    else 1

/-- Signed numerator of the unsigned Reynolds average. -/
@[reducible] def directUnsignedReynoldsEvaluation
    (assignment freeIndex : Fin 98) : ℚ :=
  let representative : PositiveRepresentativeIndex :=
    Fin.ofNat 11654 (freeColumns.getD freeIndex.1 0)
  ∑ permutation : Fin 24,
    let h := decodedHypercubicCharacterElement permutation 0
    directRepresentativeTensorSign representative h *
      directRepresentativeTraceEvaluationAt assignment representative h

@[reducible] def expectedUnsignedEvaluation
    (assignment freeIndex : Fin 98) : ℚ :=
  ((unsignedEvaluationMatrix.getD assignment.1 #[]).getD freeIndex.1 0 : ℚ)

@[reducible] def encodedEvaluationInverseFraction
    (row column : Fin 98) : Int × Nat :=
  (unsignedEvaluationInverse.getD row.1 #[]).getD column.1 (0, 1)

@[reducible] def decodedEvaluationInverse
    (row column : Fin 98) : ℚ :=
  let value := encodedEvaluationInverseFraction row column
  (value.1 : ℚ) / value.2

/-- Transparent nonnegative decoding of the absolute value.  Its equality
with rational absolute value is proved from denominator positivity. -/
@[reducible] def decodedEvaluationInverseAbs
    (row column : Fin 98) : ℚ :=
  let value := encodedEvaluationInverseFraction row column
  (value.1.natAbs : ℚ) / value.2

/-- The coefficient-sup analysis cost of one explicit dual row. -/
@[reducible] def decodedEvaluationInverseRowL1 (row : Fin 98) : ℚ :=
  ∑ column : Fin 98, decodedEvaluationInverseAbs row column

/-- Candidate sharp conditioning constant of the stored exact inverse.  Its
upper bound and attaining row are replayed independently of this definition. -/
@[reducible] def evaluationInverseConditioningConstant : ℚ :=
  4913129483781 / 245314432

end HypercubicDimension16PhysicalTraceEvaluationExecutable
end YangMills
end QuantumTheory
end Mettapedia
