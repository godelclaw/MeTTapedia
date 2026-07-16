import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalInvariantSpace

/-!
# Regression checks for the honest physical invariant space
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalInvariantSpaceRegression

open V14HypercubicFDCensus
open HypercubicDimension16PhysicalInvariantSpace

example (h : Hypercubic4) (fieldCount derivativeCount : ℕ) :
    LinearMap.trace ℚ (SectorFieldOrbitSpace fieldCount derivativeCount)
        (signedSectorFieldOrbitAction h fieldCount derivativeCount) =
      HypercubicDimension16OrbitCharacter.actualOrbitCharacter
        h fieldCount derivativeCount :=
  signedSectorFieldOrbitAction_trace h fieldCount derivativeCount

example :
    Module.finrank ℚ (sectorFieldOrbitInvariantSubmodule 8 0) = 11654 :=
  fieldEightScalarInvariantDimension

#print axioms signedSectorFieldOrbitAction_trace
#print axioms sectorFieldOrbitReynolds_isProj
#print axioms finrank_sectorFieldOrbitInvariantSubmodule
#print axioms fieldEightActualOrbitCharacter_sum_eq_encoded
#print axioms fieldEightScalarInvariantDimension

end HypercubicDimension16PhysicalInvariantSpaceRegression
end YangMills
end QuantumTheory
end Mettapedia
