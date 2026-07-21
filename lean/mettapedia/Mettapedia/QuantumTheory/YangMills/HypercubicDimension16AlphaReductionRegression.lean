import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16AlphaReduction

/-! Regression and axiom audit for the derivative-label alpha quotient. -/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16AlphaReductionRegression

open V14HypercubicFDCensus
open HypercubicUnpaddedFDSyntax
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction

example : dimension16DerivativeAlphaReducedLayoutMultiplicity = 5030751 :=
  dimension16DerivativeAlphaReducedLayoutMultiplicity_exact

example :
    Fintype.card ExactDimension16DerivativeAlphaReducedCarrier =
      21606911019319296 :=
  card_exactDimension16DerivativeAlphaReducedCarrier

example (h : Hypercubic4)
    (monomial : ExactDimension16UnpaddedRawFDMonomial) :
    exactDimension16DerivativeAlphaNormalize
        (exactDimension16UnpaddedAct h monomial) =
      exactDimension16DerivativeAlphaReducedAct h
        (exactDimension16DerivativeAlphaNormalize monomial) :=
  exactDimension16DerivativeAlphaNormalize_act h monomial

example (h : Hypercubic4)
    (monomial : ExactDimension16UnpaddedRawFDMonomial) :
    monomial.1.tensorSign h =
      exactDimension16DerivativeAlphaReducedTensorSign h
        (exactDimension16DerivativeAlphaNormalize monomial) :=
  exactDimension16DerivativeAlphaNormalize_tensorSign h monomial

#print axioms derivativeAlphaQuotientEquiv
#print axioms derivativeAlphaEquivalent_iff_existsUnique_relabel
#print axioms exactDimension16DerivativeAlphaQuotientEquiv
#print axioms card_exactDimension16DerivativeAlphaReducedCarrier
#print axioms dimension16DerivativeAlphaReducedLayoutMultiplicity_exact
#print axioms exactDimension16DerivativeAlphaNormalize_act
#print axioms exactDimension16DerivativeAlphaNormalize_tensorSign

end HypercubicDimension16AlphaReductionRegression
end YangMills
end QuantumTheory
end Mettapedia

