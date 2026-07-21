import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16JointPhysicalQuotient

/-! Regression checks for the coordinate-free joint scalar quotient. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16JointPhysicalQuotient

example (policy : PhysicalRelationPolicy)
    (value : exactFieldOrbitInvariantSubmodule) :
    value ∈ jointInvariantRelationSubmodule policy ↔
      (value.1 : ExactFieldRelabelOrbitSpace) ∈
        orbitPhysicalRelationSubmodule policy :=
  mem_jointInvariantRelationSubmodule_iff policy value

example (policy : PhysicalRelationPolicy) :
    Module.finrank ℚ (JointScalarPhysicalQuotient policy) =
      Module.finrank ℚ exactFieldOrbitInvariantSubmodule -
        Module.finrank ℚ (jointInvariantRelationSubmodule policy) :=
  jointScalarPhysicalQuotient_finrank_formula policy

example :
    jointInvariantRelationSubmodule .offShell ≤
      jointInvariantRelationSubmodule .onShell :=
  jointInvariantRelationSubmodule_offShell_le_onShell

example :
    Module.finrank ℚ (JointScalarPhysicalQuotient .onShell) ≤
      Module.finrank ℚ (JointScalarPhysicalQuotient .offShell) :=
  jointScalarPhysicalQuotient_onShell_finrank_le_offShell

#print axioms HypercubicDimension16JointPhysicalQuotient.mem_jointInvariantRelationSubmodule_iff
#print axioms HypercubicDimension16JointPhysicalQuotient.jointScalarPhysicalQuotient_finrank_formula
#print axioms HypercubicDimension16JointPhysicalQuotient.orbitPhysicalRelationOperator_liftOffShell
#print axioms HypercubicDimension16JointPhysicalQuotient.jointScalarPhysicalQuotient_onShell_finrank_le_offShell

end YangMills
end QuantumTheory
end Mettapedia
