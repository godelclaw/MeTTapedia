import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldEightPhysicalTrace
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationSemantics

/-!
# Standard trace relations vanish under the explicit matrix evaluations

The `98` stored assignments consist of traceless rational `2 x 2` matrices.
Ordinary product-of-traces evaluation therefore annihilates every standard
eight-field traceless, anticommutator, and fundamental trace row.  The result
is stated on the genuine field-relabel orbit module, before any finite chart
or rank certificate is used.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceEvaluationInvariant

open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16TraceEvaluation
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceEvaluationExecutable
open SU2LatticeFDCensusNoGo
open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

/-- The seven literal matrices in the evaluation library are traceless. -/
theorem encodedEvaluationMatrixAt_traceless
    (assignment : Fin 98) (plane : OrientedPlane) :
    Matrix.trace (encodedEvaluationMatrixAt assignment plane) = 0 := by
  decide +revert +kernel

/-- Every standard derivative-free eight-field trace row vanishes under an
arbitrary traceless plane-matrix assignment. -/
theorem fieldEightPhysicalTraceRow_evaluation_zero
    (matrices : PlaneMatrixAssignment ℚ)
    (htraceless : ∀ plane, Matrix.trace (matrices plane) = 0)
    (generator : FieldEightTraceGenerator) :
    orbitPlaneTraceEvaluationLinear matrices 8 0
        (fieldEightPhysicalTraceRow generator) = 0 := by
  cases generator with
  | traceless site =>
      rw [fieldEightPhysicalTraceRow]
      simp only [fieldEightOrbitSingle,
        orbitPlaneTraceEvaluationLinear_single, one_mul,
        orbitPlaneTraceEvaluation_mk]
      exact labeledPlaneTraceEvaluation_eq_zero_of_singleton
        matrices htraceless site.sector site.field site.singleton
  | anticommutator site =>
      simp only [fieldEightPhysicalTraceRow, map_sub, map_add,
        fieldEightOrbitSingle, orbitPlaneTraceEvaluationLinear_single,
        one_mul, orbitPlaneTraceEvaluation_mk]
      change tracePermutationContraction
            (fun field => matrices (site.sector.decoration.1 field).plane)
            site.sector.trace +
          tracePermutationContraction
            (fun field => matrices (site.sector.decoration.1 field).plane)
            (fieldEightSwapAdjacentTraceOrder site) -
          tracePermutationContraction
            (fun field => matrices (site.sector.decoration.1 field).plane)
            (fieldEightSplitAdjacentTraceOrder site) = 0
      let right := site.sector.trace site.left
      let successor := site.sector.trace right
      have hrightLeft : right ≠ site.left := by
        intro equality
        apply site.cycleLength_ge_three
        change site.sector.trace right = site.left
        rw [equality]
        exact equality
      have hsuccessorRight : successor ≠ right := by
        intro equality
        apply hrightLeft
        apply site.sector.trace.injective
        exact equality
      have hsuccessorLeft : successor ≠ site.left :=
        site.cycleLength_ge_three
      rw [fieldEightSwapAdjacentTraceOrder,
        fieldEightSplitAdjacentTraceOrder,
        adjacentForwardRewire_eq_threeTargetCycleForward
          site.left right successor hsuccessorRight.symm
          hrightLeft hsuccessorLeft,
        Equiv.swap_comm site.left successor]
      exact tracePermutationContraction_anticommutator_rewire
        (fun field => matrices (site.sector.decoration.1 field).plane)
        (fun field => htraceless _) site.sector.trace site.left
        site.cycleLength_ge_three
  | fundamental site =>
      simp only [fieldEightPhysicalTraceRow, map_sub, map_add,
        fieldEightOrbitSingle, orbitPlaneTraceEvaluationLinear_single,
        one_mul, orbitPlaneTraceEvaluation_mk]
      change tracePermutationContraction
            (fun field => matrices (site.sector.decoration.1 field).plane)
            site.sector.trace -
          tracePermutationContraction
            (fun field => matrices (site.sector.decoration.1 field).plane)
            (site.sector.trace.trans
              (Equiv.swap (site.label 0) (site.label 1))) -
          tracePermutationContraction
            (fun field => matrices (site.sector.decoration.1 field).plane)
            (site.sector.trace.trans
              (Equiv.swap (site.label 0) (site.label 2))) -
          tracePermutationContraction
            (fun field => matrices (site.sector.decoration.1 field).plane)
            (site.sector.trace.trans
              (Equiv.swap (site.label 1) (site.label 2))) +
          tracePermutationContraction
            (fun field => matrices (site.sector.decoration.1 field).plane)
            (site.sector.trace.trans
              (fieldEightFundamentalCycleForward site)) +
          tracePermutationContraction
            (fun field => matrices (site.sector.decoration.1 field).plane)
            (site.sector.trace.trans
              (fieldEightFundamentalCycleBackward site)) = 0
      simpa [fieldEightFundamentalCycleForward,
        fieldEightFundamentalCycleBackward, threeTargetCycleForward,
        threeTargetCycleBackward] using
        tracePermutationContraction_fundamental_rewire
          (fun field => matrices (site.sector.decoration.1 field).plane)
          site.sector.trace (site.label 0) (site.label 1) (site.label 2)
          (site.label.injective.ne (by decide))
          (site.label.injective.ne (by decide))
          (site.label.injective.ne (by decide))

/-- The explicit assignment, after any literal hypercubic transport, still
annihilates every standard trace row. -/
theorem fieldEightPhysicalTraceRow_encoded_evaluation_zero
    (assignment : Fin 98) (h : Hypercubic4)
    (generator : FieldEightTraceGenerator) :
    orbitPlaneTraceEvaluationLinear
        (fun plane => encodedEvaluationMatrixAt assignment
          (planeAction h plane)) 8 0
        (fieldEightPhysicalTraceRow generator) = 0 := by
  apply fieldEightPhysicalTraceRow_evaluation_zero
  intro plane
  exact encodedEvaluationMatrixAt_traceless assignment (planeAction h plane)

end HypercubicDimension16PhysicalTraceEvaluationInvariant
end YangMills
end QuantumTheory
end Mettapedia
