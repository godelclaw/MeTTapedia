import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalOrbitOperator

/-!
# Regression checks for the physical operator on field-label orbits
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalOrbitOperatorRegression

open V14HypercubicFDCensus
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator

example : Function.Surjective normalizeExactFieldRelabel :=
  normalizeExactFieldRelabel_surjective

example (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : PhysicalRelationGeneratorSpace policy) :
    orbitPhysicalRelationOperator policy
        (signedPhysicalRelationGeneratorAction policy h value) =
      signedExactFieldRelabelOrbitAction h
        (orbitPhysicalRelationOperator policy value) :=
  orbitPhysicalRelationOperator_equivariant policy h value

#print axioms normalizeExactFieldRelabel_surjective
#print axioms ker_normalizeExactFieldRelabel_eq_relationSubmodule
#print axioms exactFieldRelabelRelationQuotientEquiv
#print axioms signedExactFieldRelabelOrbitRepresentation
#print axioms normalizeExactFieldRelabel_signed_equivariant
#print axioms orbitPhysicalRelationOperator_equivariant
#print axioms orbitPhysicalRelationSubmodule_signed_invariant

end HypercubicDimension16PhysicalOrbitOperatorRegression
end YangMills
end QuantumTheory
end Mettapedia
