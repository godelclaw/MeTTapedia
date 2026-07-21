import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16ShuffleLinearQuotient

/-!
# Regression checks for the exact linear derivative-shuffle quotient
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16ShuffleLinearQuotientRegression

open HypercubicDimension16ShuffleLinearQuotient

theorem literal_adjacent_rows_are_the_full_linear_kernel
    (fieldCount derivativeCount : ℕ) :
    LinearMap.ker (linearLocalize fieldCount derivativeCount) =
      literalShuffleSubmodule fieldCount derivativeCount :=
  ker_linearLocalize_eq_literalShuffleSubmodule fieldCount derivativeCount

def literal_linear_quotient_is_local_word_space
    (fieldCount derivativeCount : ℕ) :
    (GlobalOwnedAxisWordSpace fieldCount derivativeCount ⧸
        literalShuffleSubmodule fieldCount derivativeCount) ≃ₗ[ℚ]
      LocalAxisWordFamilySpace fieldCount derivativeCount :=
  literalShuffleQuotientEquivLocal fieldCount derivativeCount

#print axioms semanticShuffleEquivalent_generatedVector
#print axioms ker_linearLocalize_eq_literalShuffleSubmodule
#print axioms literalShuffleQuotientEquivLocal

end HypercubicDimension16ShuffleLinearQuotientRegression
end YangMills
end QuantumTheory
end Mettapedia
