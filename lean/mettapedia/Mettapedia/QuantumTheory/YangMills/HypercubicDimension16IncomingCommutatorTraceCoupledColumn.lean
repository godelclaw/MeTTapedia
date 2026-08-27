import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceProjection

/-!
# OUR full cross-sector incoming commutator column

The concrete covariant commutator used in the incoming trace comparison is
not an eight-field relation.  This module records its full exact orbit-carrier
column: two seven-field derivative terms and two eight-field curvature
insertions.  It supplies the literal cross-sector datum required by a coupled
quotient construction.

No quotient dimension or complete-relation claim is made here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IncomingCommutatorTraceCoupledColumn

open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16IncomingCommutatorTraceMismatch

/-- OUR exact target of the unswapped seven-field derivative source. -/
def ourCommutatorSourceExactTarget : ExactFieldRelabelOrbitCarrier :=
  exactFieldRelabelOrbitOfOriented
    (exactNormalizedSectorData ourFieldSevenCommutatorCarrier)

/-- OUR exact target of the derivative-swapped seven-field source. -/
def ourCommutatorSwappedExactTarget : ExactFieldRelabelOrbitCarrier :=
  exactFieldRelabelOrbitOfOriented
    (exactNormalizedSectorData
      (swapExactDerivativePositions ourFieldSevenCommutatorCarrier
        ourFieldSevenCommutatorSite.outer ourFieldSevenCommutatorSite.inner))

theorem ourCommutator_source_orientationCoefficient :
    fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment ourFieldSevenCommutatorCarrier.2) = 1 := by
  decide +kernel

theorem ourCommutator_swapped_orientationCoefficient :
    fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment
          (swapExactDerivativePositions ourFieldSevenCommutatorCarrier
            ourFieldSevenCommutatorSite.outer
            ourFieldSevenCommutatorSite.inner).2) = 1 := by
  decide +kernel

/-- The exact physical column of OUR concrete commutator contains both its
seven-field derivative difference and its eight-field curvature difference. -/
theorem orbitPhysicalRelationOperator_ourCommutator_full
    (policy : PhysicalRelationPolicy) :
    orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1) =
      Finsupp.single ourCommutatorSourceExactTarget 1 -
        Finsupp.single ourCommutatorSwappedExactTarget 1 -
          Finsupp.single
            (ourCommutatorInsertionExactTarget CurvatureInsertionSide.before) 1 +
            Finsupp.single
              (ourCommutatorInsertionExactTarget CurvatureInsertionSide.after) 1 := by
  simp only [orbitPhysicalRelationOperator,
    normalizedPhysicalRelationOperator,
    LinearMap.comp_apply, physicalRelationOperator_single, one_smul,
    ourFieldSevenCommutatorGenerator, physicalRelationRow,
    covariantCommutatorRow, map_sub, map_add,
    normalizeExactContextual_single]
  simp_rw [our_normalizeExactContextualBasis_fieldRelabel]
  rw [exactFieldRelabelOrbitOfOriented_ourCommutatorInsertion,
    exactFieldRelabelOrbitOfOriented_ourCommutatorInsertion,
    ourCommutator_source_orientationCoefficient,
    ourCommutator_swapped_orientationCoefficient,
    ourCommutator_before_orientationCoefficient,
    ourCommutator_after_orientationCoefficient]
  rfl

#print axioms orbitPhysicalRelationOperator_ourCommutator_full

end HypercubicDimension16IncomingCommutatorTraceCoupledColumn
end YangMills
end QuantumTheory
end Mettapedia
