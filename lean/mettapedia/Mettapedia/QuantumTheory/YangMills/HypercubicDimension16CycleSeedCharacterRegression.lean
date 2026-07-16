import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CycleSeedCharacter

/-!
# Regression checks for the dependent cycle-seed character
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CycleSeedCharacterRegression

open V14HypercubicFDCensus
open HypercubicDimension16CompressionCensus
open HypercubicDimension16CycleSeedCharacter

theorem exact_cycle_seed_convolution
    (h : Hypercubic4) (parts : List ℕ) (remainingDegree : ℕ) :
    cycleSeedCharacter h parts remainingDegree =
      partitionDerivativeCharacter h parts remainingDegree :=
  cycleSeedCharacter_eq_partitionDerivativeCharacter
    h parts remainingDegree

#print axioms signedFixedProductSum
#print axioms cycleSeedCharacter_cons
#print axioms cycleSeedCharacter_eq_partitionDerivativeCharacter

end HypercubicDimension16CycleSeedCharacterRegression
end YangMills
end QuantumTheory
end Mettapedia
