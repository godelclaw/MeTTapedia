import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalRelationBlocks

/-!
# Regression checks for the physical relation sector blocks
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalRelationBlocksRegression

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationBlocks

example {policy : PhysicalRelationPolicy}
    (generator : PhysicalRelationGenerator policy)
    (coefficient : ℚ)
    (target : ExactFieldRelabelOrbitCarrier)
    (outside : ¬ InSourceOrSuccessorFieldSector
      (physicalRelationGeneratorSourceFieldCount generator) target.1) :
    orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient) target = 0 :=
  orbitPhysicalRelationOperator_single_apply_eq_zero_of_outside_field_band
    generator coefficient target outside

#print axioms physicalRelationRow_apply_eq_zero_of_outside_field_band
#print axioms normalizeExactContextual_fieldFilter
#print axioms normalizeExactFieldRelabel_fieldFilter
#print axioms relationFieldFilter_physicalRelationRow
#print axioms orbitPhysicalRelationOperator_single_field_band
#print axioms orbitPhysicalRelationOperator_single_apply_eq_zero_of_outside_field_band

end HypercubicDimension16PhysicalRelationBlocksRegression
end YangMills
end QuantumTheory
end Mettapedia
