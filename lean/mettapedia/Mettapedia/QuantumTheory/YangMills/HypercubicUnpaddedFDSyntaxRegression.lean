import Mettapedia.QuantumTheory.YangMills.HypercubicUnpaddedFDSyntax

/-! Regression and axiom audit for the unpadded finite `F,D` syntax. -/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicUnpaddedFDSyntaxRegression

open V14HypercubicFDCensus
open HypercubicUnpaddedFDSyntax

example : Finite UnpaddedRawFDMonomial :=
  unpaddedRawFDCensus_finite

example (monomial : UnpaddedRawFDMonomial) :
    monomial.canonicalDimension ≤ 16 :=
  monomial.canonicalDimension_le_sixteen

example (left right : Hypercubic4) (monomial : UnpaddedRawFDMonomial) :
    monomial.act (Hypercubic4.compose left right) =
      (monomial.act right).act left :=
  monomial.act_compose left right

example : Fintype.card (UnpaddedFDSector 2 12) =
    16853370525545870131200 := by
  rw [card_unpaddedFDSector]
  norm_num [Nat.factorial]

example : 16853370525545870131200 ≤
    Fintype.card UnpaddedRawFDMonomial :=
  card_unpaddedRawFDCensus_lower_bound

#print axioms UnpaddedRawFDMonomial.act_compose
#print axioms UnpaddedRawFDMonomial.tensorSign_compose
#print axioms card_unpaddedRawFDCensus_lower_bound
#print axioms ext_active

end HypercubicUnpaddedFDSyntaxRegression
end YangMills
end QuantumTheory
end Mettapedia
