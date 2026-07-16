import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16RelationEquivariance

/-! Regression and axiom audit for the first standard relation rows. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16RelationEquivarianceRegression

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance

example (h : Hypercubic4) (carrier : RelationCarrier)
    (slot : Fin carrier.1.1) :
    signedRelationAction h (fieldAntisymmetryRow carrier slot) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        fieldAntisymmetryRow
          (exactDimension16DerivativeAlphaReducedAct h carrier) slot :=
  fieldAntisymmetryRow_equivariant h carrier slot

example (h : Hypercubic4) (carrier : RelationCarrier)
    (left right : Fin (dimension16DerivativeCount carrier.1))
    (hdifferent :
      carrier.2.derivativeWord.ownerAtPosition left ≠
        carrier.2.derivativeWord.ownerAtPosition right) :
    signedRelationAction h (derivativeShuffleRow carrier left right) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        derivativeShuffleRow
          (exactDimension16DerivativeAlphaReducedAct h carrier)
          left right :=
  derivativeShuffleRow_equivariant h carrier left right hdifferent

example (h : Hypercubic4) (carrier : RelationCarrier)
    (rename : Equiv.Perm (Fin carrier.1.1)) :
    signedRelationAction h (fieldAlphaRow carrier rename) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        fieldAlphaRow
          (exactDimension16DerivativeAlphaReducedAct h carrier) rename :=
  fieldAlphaRow_equivariant h carrier rename

#print axioms signedRelationAction_single
#print axioms fieldAntisymmetryRow_equivariant
#print axioms derivativeShuffleRow_equivariant
#print axioms fieldAlphaRow_equivariant

end HypercubicDimension16RelationEquivarianceRegression
end YangMills
end QuantumTheory
end Mettapedia

