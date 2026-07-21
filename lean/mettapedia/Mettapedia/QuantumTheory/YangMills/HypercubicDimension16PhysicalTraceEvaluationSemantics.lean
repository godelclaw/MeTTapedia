import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationExecutable
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceEvaluation

/-!
# Semantic matrix evaluation of the free four-pair trace sector

The free columns in the physical trace quotient have four two-letter trace
cycles.  This file relates their transparent product-of-traces evaluator to
the standard matrix-index contraction on the genuine labeled carrier.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceEvaluationSemantics

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDCharacterCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16TraceEvaluation
open HypercubicDimension16TraceOrbitChart
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitExecutableSignature
open HypercubicDimension16PhysicalTraceEvaluationData
open HypercubicDimension16PhysicalTraceEvaluationExecutable

/-! ## Trace contraction under an arbitrary label equivalence -/

def transportMatrixIndexState {Source Target : Type*}
    (rename : Source ≃ Target) :
    (Source → Fin 2) ≃ (Target → Fin 2) :=
  Equiv.arrowCongr rename (Equiv.refl _)

@[simp] theorem transportMatrixIndexState_apply
    {Source Target : Type*} (rename : Source ≃ Target)
    (state : Source → Fin 2) (field : Target) :
    transportMatrixIndexState rename state field =
      state (rename.symm field) := by
  rfl

/-- Matrix-index contraction is invariant under a change of its finite label
type, not merely under a permutation of one fixed type. -/
theorem tracePermutationContraction_equiv
    {Source Target R : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    [CommSemiring R]
    (rename : Source ≃ Target)
    (matrixAt : Source → Matrix (Fin 2) (Fin 2) R)
    (traceOrder : Equiv.Perm Source) :
    tracePermutationContraction (matrixAt ∘ rename.symm)
        (rename.symm.trans (traceOrder.trans rename)) =
      tracePermutationContraction matrixAt traceOrder := by
  let summand : (Target → Fin 2) → R := fun state =>
    ∏ field : Target,
      (matrixAt ∘ rename.symm) field
        (state field)
        (state ((rename.symm.trans (traceOrder.trans rename)) field))
  calc
    tracePermutationContraction (matrixAt ∘ rename.symm)
        (rename.symm.trans (traceOrder.trans rename)) =
        ∑ state : Target → Fin 2, summand state := rfl
    _ = ∑ state : Source → Fin 2,
          summand (transportMatrixIndexState rename state) := by
      exact (Equiv.sum_comp (transportMatrixIndexState rename) summand).symm
    _ = ∑ state : Source → Fin 2,
          ∏ field : Source,
            matrixAt field (state field) (state (traceOrder field)) := by
      apply Finset.sum_congr rfl
      intro state _
      unfold summand
      simp only [Function.comp_apply, transportMatrixIndexState_apply,
        Equiv.trans_apply, Equiv.symm_apply_apply]
      change (∏ field : Target,
          matrixAt (rename.symm field)
            (state (rename.symm field))
            (state (traceOrder (rename.symm field)))) =
        ∏ field : Source,
          matrixAt field (state field) (state (traceOrder field))
      exact Equiv.prod_comp rename.symm
        (fun field =>
          matrixAt field (state field) (state (traceOrder field)))
    _ = tracePermutationContraction matrixAt traceOrder := rfl

/-! ## Four independent two-letter cycles -/

/-- The trace permutation which swaps the two positions in each pair. -/
def pairedTraceOrder (Pair : Type*) : Equiv.Perm (Pair × Fin 2) :=
  Equiv.prodCongr (Equiv.refl Pair) (Equiv.swap 0 1)

@[simp] theorem pairedTraceOrder_apply
    {Pair : Type*} (pair : Pair) (position : Fin 2) :
    pairedTraceOrder Pair (pair, position) =
      (pair, Equiv.swap 0 1 position) := by
  rfl

theorem twoCycleStateSum_eq_trace_mul
    {R : Type*} [CommSemiring R]
    (left right : Matrix (Fin 2) (Fin 2) R) :
    (∑ state : Fin 2 → Fin 2,
      left (state 0) (state 1) * right (state 1) (state 0)) =
      Matrix.trace (left * right) := by
  let summand : (Fin 2 → Fin 2) → R := fun state =>
    left (state 0) (state 1) * right (state 1) (state 0)
  calc
    (∑ state : Fin 2 → Fin 2,
        left (state 0) (state 1) * right (state 1) (state 0)) =
        ∑ state : Fin 2 → Fin 2, summand state := rfl
    _ = ∑ data : Fin 2 × Fin 2,
          summand ((finTwoArrowEquiv (Fin 2)).symm data) := by
      exact (Equiv.sum_comp (finTwoArrowEquiv (Fin 2)).symm summand).symm
    _ = ∑ data : Fin 2 × Fin 2,
          left data.1 data.2 * right data.2 data.1 := by
      apply Finset.sum_congr rfl
      rintro ⟨first, second⟩ _
      simp [summand]
    _ = Matrix.trace (left * right) := by
      simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]

/-- A disjoint union of two-cycles contracts to the product of the ordinary
matrix traces around those cycles. -/
theorem tracePermutationContraction_paired
    {Pair R : Type*} [Fintype Pair] [DecidableEq Pair]
    [CommSemiring R]
    (matrixAt : Pair × Fin 2 → Matrix (Fin 2) (Fin 2) R) :
    tracePermutationContraction matrixAt (pairedTraceOrder Pair) =
      ∏ pair : Pair,
        Matrix.trace (matrixAt (pair, 0) * matrixAt (pair, 1)) := by
  let summand : (Pair × Fin 2 → Fin 2) → R := fun state =>
    ∏ field : Pair × Fin 2,
      matrixAt field (state field)
        (state (pairedTraceOrder Pair field))
  calc
    tracePermutationContraction matrixAt (pairedTraceOrder Pair) =
        ∑ state : Pair × Fin 2 → Fin 2, summand state := rfl
    _ = ∑ state : Pair → Fin 2 → Fin 2,
          summand ((Equiv.curry Pair (Fin 2) (Fin 2)).symm state) := by
      exact (Equiv.sum_comp
        (Equiv.curry Pair (Fin 2) (Fin 2)).symm summand).symm
    _ = ∑ state : Pair → Fin 2 → Fin 2,
          ∏ pair : Pair, ∏ position : Fin 2,
            matrixAt (pair, position)
              (state pair position)
              (state pair (Equiv.swap 0 1 position)) := by
      apply Finset.sum_congr rfl
      intro state _
      unfold summand
      rw [Fintype.prod_prod_type]
      rfl
    _ = ∏ pair : Pair,
          ∑ state : Fin 2 → Fin 2,
            ∏ position : Fin 2,
              matrixAt (pair, position)
                (state position)
                (state (Equiv.swap 0 1 position)) := by
      rw [Fintype.prod_sum]
    _ = ∏ pair : Pair,
          ∑ state : Fin 2 → Fin 2,
            matrixAt (pair, 0) (state 0) (state 1) *
              matrixAt (pair, 1) (state 1) (state 0) := by
      apply Finset.prod_congr rfl
      intro pair _
      apply Finset.sum_congr rfl
      intro state _
      rw [Fin.prod_univ_two]
      simp
    _ = ∏ pair : Pair,
          Matrix.trace (matrixAt (pair, 0) * matrixAt (pair, 1)) := by
      apply Finset.prod_congr rfl
      intro pair _
      exact twoCycleStateSum_eq_trace_mul
        (matrixAt (pair, 0)) (matrixAt (pair, 1))

/-- Pair-major identification `(pair, position) ↦ 2 * pair + position`. -/
def fourPairLabelEquiv : Fin 4 × Fin 2 ≃ Fin 8 :=
  finProdFinEquiv

/-- The four-pair trace order on the eight literal field labels. -/
def fourPairTraceOrder : Equiv.Perm (Fin 8) :=
  fourPairLabelEquiv.symm.trans
    ((pairedTraceOrder (Fin 4)).trans fourPairLabelEquiv)

theorem tracePermutationContraction_fourPair
    {R : Type*} [CommSemiring R]
    (matrixAt : Fin 8 → Matrix (Fin 2) (Fin 2) R) :
    tracePermutationContraction matrixAt fourPairTraceOrder =
      ∏ pair : Fin 4,
        Matrix.trace
          (matrixAt (fourPairLabelEquiv (pair, 0)) *
            matrixAt (fourPairLabelEquiv (pair, 1))) := by
  have hrelabel := tracePermutationContraction_equiv
    fourPairLabelEquiv (matrixAt ∘ fourPairLabelEquiv)
      (pairedTraceOrder (Fin 4))
  exact hrelabel.trans <|
    tracePermutationContraction_paired
      (matrixAt ∘ fourPairLabelEquiv)

/-! ## Checked free columns and their semantic evaluator -/

def freeRepresentativeIndex (index : Fin 98) :
    PositiveRepresentativeIndex :=
  Fin.ofNat 11654 (freeColumns.getD index.1 0)

@[reducible] def FreeRepresentativeHasFourPairTrace
    (index : Fin 98) : Prop :=
  ∀ field : Fin 8,
    encodedTraceForward
        (positiveRepresentativeCode (freeRepresentativeIndex index)) field =
      fourPairTraceOrder field

def fourPairRepresentativeTraceEvaluationAt
    (assignment : Fin 98) (index : PositiveRepresentativeIndex)
    (h : Hypercubic4) : ℚ :=
  ∏ pair : Fin 4,
    Matrix.trace
      (encodedEvaluationMatrixAt assignment
          (planeAction h
            (encodedPlane (positiveRepresentativeCode index)
              (fourPairLabelEquiv (pair, 0)))) *
        encodedEvaluationMatrixAt assignment
          (planeAction h
            (encodedPlane (positiveRepresentativeCode index)
              (fourPairLabelEquiv (pair, 1)))))

/-- Signed numerator of the unsigned Reynolds evaluation on the checked
four-pair free columns. -/
def fourPairUnsignedReynoldsEvaluation
    (assignment freeIndex : Fin 98) : ℚ :=
  ∑ permutation : Fin 24,
    let h := decodedHypercubicCharacterElement permutation 0
    directRepresentativeTensorSign (freeRepresentativeIndex freeIndex) h *
      fourPairRepresentativeTraceEvaluationAt assignment
        (freeRepresentativeIndex freeIndex) h

theorem fourPairRepresentativeTraceEvaluationAt_eq_labeled
    (htrace : ∀ freeIndex : Fin 98,
      FreeRepresentativeHasFourPairTrace freeIndex)
    (assignment freeIndex : Fin 98) (h : Hypercubic4) :
    fourPairRepresentativeTraceEvaluationAt assignment
        (freeRepresentativeIndex freeIndex) h =
      labeledPlaneTraceEvaluation
        (fun plane => encodedEvaluationMatrixAt assignment
          (planeAction h plane))
        (decodedPositiveRepresentative
          (freeRepresentativeIndex freeIndex)) := by
  let sector := decodedPositiveRepresentative
    (freeRepresentativeIndex freeIndex)
  have htraceOrder : sector.trace = fourPairTraceOrder := by
    apply Equiv.ext
    intro field
    exact htrace freeIndex field
  unfold labeledPlaneTraceEvaluation
  rw [htraceOrder, tracePermutationContraction_fourPair]
  rfl

end HypercubicDimension16PhysicalTraceEvaluationSemantics
end YangMills
end QuantumTheory
end Mettapedia
