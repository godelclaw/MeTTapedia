import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16DifferentialRelations

/-! Regression and axiom audit for the Bianchi and EOM rows. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16DifferentialRelationsRegression

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16DifferentialRelations

example (h : Hypercubic4) (carrier : RelationCarrier)
    (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (hinnermost : IsInnermostDerivative carrier field position) :
    signedRelationAction h (bianchiRow carrier field position) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        bianchiRow
          (exactDimension16DerivativeAlphaReducedAct h carrier)
          field position :=
  bianchiRow_equivariant h carrier field position hinnermost

example (h : Hypercubic4) (carrier : RelationCarrier)
    (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (hinnermost : IsInnermostDerivative carrier field position) :
    signedRelationAction h (eomRow carrier field position) =
      eomContextSign h carrier field position •
        eomRow (exactDimension16DerivativeAlphaReducedAct h carrier)
          field position :=
  eomRow_equivariant h carrier field position hinnermost

#print axioms setFieldDerivativeAxes_act
#print axioms setFieldDerivativeAxes_tensorSign
#print axioms bianchiRow_equivariant
#print axioms eomRow_equivariant

end HypercubicDimension16DifferentialRelationsRegression
end YangMills
end QuantumTheory
end Mettapedia

