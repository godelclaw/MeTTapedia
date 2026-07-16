import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16ConjugacyCompression

/-!
# Regression checks for exact conjugacy compression
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16ConjugacyCompressionRegression

open HypercubicDimension16CompressionCensus
open HypercubicDimension16OrbitCharacter
open HypercubicDimension16ConjugacyCompression
open V14HypercubicFDCensus

theorem honest_orbit_character_is_partition_character
    (h : Hypercubic4) (fieldIndex : Fin 8) :
    actualOrbitCharacter h (fieldIndex.1 + 1)
        (derivativeCountForFields (fieldIndex.1 + 1)) =
      compressedSectorCharacter h (fieldIndex.1 + 1) :=
  actualOrbitCharacter_eq_compressedSectorCharacter h fieldIndex

#print axioms permutationStandardPartition_eq_iff_isConj
#print axioms partitionFiberEquivIsConj
#print axioms conjugacyClassCard_mul_centralizerCard_eq_factorial
#print axioms labeledBurnsideNumerator_eq_factorial_mul_compressedSectorCharacter
#print axioms actualOrbitCharacter_eq_compressedSectorCharacter

end HypercubicDimension16ConjugacyCompressionRegression
end YangMills
end QuantumTheory
end Mettapedia
