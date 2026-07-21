import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LocalLetterCharacter

/-!
# Regression checks for the exact local-letter character
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16LocalLetterCharacterRegression

open V14HypercubicFDCensus
open HypercubicDimension16CompressionCensus
open HypercubicDimension16LocalLetterCharacter

theorem exact_cycle_seed_character
    (h : Hypercubic4) (cycleLength derivativeCount : ℕ) :
    exactLocalLetterCharacter (h ^ cycleLength) derivativeCount =
      cycleLetterCharacter h cycleLength derivativeCount :=
  exactLocalLetterCharacter_eq_cycleLetterCharacter
    h cycleLength derivativeCount

theorem dependent_local_letter_fiber_character
    (h : Hypercubic4) (cycleLength derivativeBudget derivativeCount : ℕ)
    (countBound : derivativeCount ≤ derivativeBudget) :
    localFieldLetterFiberCharacter (h ^ cycleLength)
        derivativeBudget derivativeCount =
      cycleLetterCharacter h cycleLength derivativeCount := by
  rw [localFieldLetterFiberCharacter_eq_exact _ _ _ countBound,
    exactLocalLetterCharacter_eq_cycleLetterCharacter]

#print axioms signedFixedPlaneSum_eq_twoFormCharacter
#print axioms signedFixedAxisWordSum_eq_vectorCharacter_pow
#print axioms localFieldLetterFiberCharacter_eq_exact
#print axioms exactLocalLetterCharacter_eq_cycleLetterCharacter

end HypercubicDimension16LocalLetterCharacterRegression
end YangMills
end QuantumTheory
end Mettapedia
