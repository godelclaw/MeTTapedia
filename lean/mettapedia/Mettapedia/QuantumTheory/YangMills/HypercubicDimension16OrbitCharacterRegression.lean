import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16OrbitCharacter

/-!
# Regression checks for the actual orbit character and weighted Burnside bridge
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16OrbitCharacterRegression

open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16OrbitCharacter
open V14HypercubicFDCensus

theorem honest_carrier_weighted_burnside
    (h : Hypercubic4) (fieldCount derivativeCount : ℕ) :
    labeledBurnsideNumerator h fieldCount derivativeCount =
      Nat.factorial fieldCount *
        actualOrbitCharacter h fieldCount derivativeCount :=
  labeledBurnsideNumerator_eq_factorial_mul_actualOrbitCharacter
    h fieldCount derivativeCount

theorem identity_character_is_orbit_cardinality
    (fieldCount derivativeCount : ℕ) :
    actualOrbitCharacter 1 fieldCount derivativeCount =
      Fintype.card (FieldRelabelOrbitCarrier fieldCount derivativeCount) :=
  actualOrbitCharacter_one fieldCount derivativeCount

#print axioms WeightedOrbitBurnside.labeledTwistedWeightSum_eq_card_mul_quotientFixedWeightSum
#print axioms actualOrbitCharacter
#print axioms labeledBurnsideNumerator_eq_factorial_mul_actualOrbitCharacter
#print axioms actualOrbitCharacter_one

end HypercubicDimension16OrbitCharacterRegression
end YangMills
end QuantumTheory
end Mettapedia
