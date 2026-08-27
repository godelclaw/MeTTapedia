import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16ContextualQuotient

/-!
# Regression checks for the exact contextual quotient
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16ContextualQuotientRegression

open HypercubicDimension16ContextualQuotient
open HypercubicDimension16RelationEquivariance
open V14HypercubicFDCensus

theorem fixed_sector_literal_rows_are_the_full_kernel
    (fieldCount derivativeCount : ℕ) :
    LinearMap.ker (normalizeContextualSector fieldCount derivativeCount) =
      contextualRelationSubmodule fieldCount derivativeCount :=
  ker_normalizeContextualSector_eq_contextualRelationSubmodule
    fieldCount derivativeCount

theorem actual_dimension16_operators_are_the_full_kernel :
    LinearMap.ker normalizeExactContextual =
      exactOperatorRelationSubmodule :=
  ker_normalizeExactContextual_eq_exactOperatorRelationSubmodule

def actual_dimension16_operator_quotient :
    (RelationSpace ⧸ exactOperatorRelationSubmodule) ≃ₗ[ℚ]
      ExactOrientedLocalSpace :=
  exactOperatorRelationQuotientEquiv

theorem exact_normalization_is_signed_hypercubic_equivariant
    (h : Hypercubic4) (value : RelationSpace) :
    normalizeExactContextual (signedRelationAction h value) =
      signedExactOrientedLocalAction h
        (normalizeExactContextual value) :=
  normalizeExactContextual_signed_equivariant h value

#print axioms ker_normalizeContextualSector_eq_contextualRelationSubmodule
#print axioms ker_normalizeExactContextual_eq_exactOperatorRelationSubmodule
#print axioms exactOperatorRelationQuotientEquiv
#print axioms normalizeExactContextual_signed_equivariant

end HypercubicDimension16ContextualQuotientRegression
end YangMills
end QuantumTheory
end Mettapedia
