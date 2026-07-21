import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FixedCycleFamilyCarrier

/-!
# Regression checks for the dependent fixed-cycle-family carrier
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16FixedCycleFamilyCarrierRegression

open V14HypercubicFDCensus
open HypercubicDimension16CompressionCensus
open HypercubicDimension16FixedCycleFamilyCarrier

theorem exact_positive_cycle_list_character
    (h : Hypercubic4) (parts : List ℕ) (remainingDegree : ℕ)
    (positiveParts : ∀ cycleLength ∈ parts, 0 < cycleLength) :
    fixedCycleFamilyCharacter h parts remainingDegree =
      partitionDerivativeCharacter h parts remainingDegree :=
  fixedCycleFamilyCharacter_eq_partitionDerivativeCharacter
    h parts remainingDegree positiveParts

#print axioms fixedCycleFamilyCharacter_cons_succ
#print axioms fixedCycleFamilyCharacter_eq_cycleSeedCharacter
#print axioms fixedCycleFamilyCharacter_eq_partitionDerivativeCharacter

end HypercubicDimension16FixedCycleFamilyCarrierRegression
end YangMills
end QuantumTheory
end Mettapedia
