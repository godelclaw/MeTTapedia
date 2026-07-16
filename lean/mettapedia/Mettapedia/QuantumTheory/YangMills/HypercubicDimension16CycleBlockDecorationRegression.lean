import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CycleBlockDecoration

/-!
# Regression checks for concrete disjoint-cycle decorations
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CycleBlockDecorationRegression

open V14HypercubicFDCensus
open HypercubicDimension16CompressionCensus
open HypercubicDimension16CycleBlockDecoration

theorem concrete_block_label_count (parts : List ℕ) :
    Fintype.card (CycleBlockLabel parts) = parts.sum :=
  card_cycleBlockLabel parts

theorem exact_concrete_block_character
    (h : Hypercubic4) (parts : List ℕ) (targetDegree : ℕ)
    (positiveParts : ∀ cycleLength ∈ parts, 0 < cycleLength) :
    cycleBlockDecorationCharacter h parts targetDegree targetDegree =
      partitionDerivativeCharacter h parts targetDegree :=
  cycleBlockDecorationCharacter_eq_partitionDerivativeCharacter
    h parts targetDegree positiveParts

#print axioms card_cycleBlockLabel
#print axioms fixedCycleBlockDecorationEquivBudgetedCarrier
#print axioms cycleBlockDecorationCharacter_eq_budgetedCarrierCharacter
#print axioms cycleBlockDecorationCharacter_eq_partitionDerivativeCharacter

end HypercubicDimension16CycleBlockDecorationRegression
end YangMills
end QuantumTheory
end Mettapedia
