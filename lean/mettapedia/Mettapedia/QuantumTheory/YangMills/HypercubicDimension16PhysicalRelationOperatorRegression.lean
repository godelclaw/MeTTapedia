import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalRelationOperator

/-!
# Regression checks for the equivariant physical relation operator
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalRelationOperatorRegression

open V14HypercubicFDCensus
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16PhysicalRelationOperator

example (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : PhysicalRelationGeneratorSpace policy) :
    physicalRelationOperator policy
        (signedPhysicalRelationGeneratorAction policy h value) =
      signedRelationAction h (physicalRelationOperator policy value) :=
  physicalRelationOperator_equivariant policy h value

example (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : PhysicalRelationGeneratorSpace policy) :
    normalizedPhysicalRelationOperator policy
        (signedPhysicalRelationGeneratorAction policy h value) =
      signedExactOrientedLocalAction h
        (normalizedPhysicalRelationOperator policy value) :=
  normalizedPhysicalRelationOperator_equivariant policy h value

#print axioms signedRelationRepresentation
#print axioms signedExactOrientedLocalRepresentation
#print axioms signedPhysicalRelationGeneratorRepresentation
#print axioms physicalRelationOperator_equivariant
#print axioms physicalRelationSubmodule_signed_invariant
#print axioms normalizedPhysicalRelationOperator_equivariant
#print axioms normalizedPhysicalRelationSubmodule_signed_invariant

end HypercubicDimension16PhysicalRelationOperatorRegression
end YangMills
end QuantumTheory
end Mettapedia
