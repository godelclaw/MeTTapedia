import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CycleFamilyCharacter

/-!
# Regression checks for the one-cycle fixed-family character
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CycleFamilyCharacterRegression

open V14HypercubicFDCensus
open HypercubicDimension16LocalLetterCharacter
open HypercubicDimension16CycleFamilyCharacter

theorem exact_one_cycle_character
    (h : Hypercubic4) (cyclePredecessor derivativeCount : ℕ) :
    exactCycleFamilyCharacter h cyclePredecessor derivativeCount =
      exactLocalLetterCharacter (h ^ (cyclePredecessor + 1))
        derivativeCount :=
  exactCycleFamilyCharacter_eq_exactLocalLetterCharacter
    h cyclePredecessor derivativeCount

#print axioms ExactLocalFieldLetter.tensorSign_pow_eq_prod
#print axioms fixedExactCycleFamily_eq_seed_power
#print axioms fixedExactCycleFamily_tensorSign
#print axioms exactCycleFamilyCharacter_eq_exactLocalLetterCharacter

end HypercubicDimension16CycleFamilyCharacterRegression
end YangMills
end QuantumTheory
end Mettapedia
