import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IBPTraceRelations

/-! Regression and axiom audit for IBP and traceless-letter rows. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IBPTraceRelationsRegression

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16IBPTraceRelations

example (h : Hypercubic4) (carrier : RelationCarrier)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (houtermost : IsGloballyOutermostDerivative carrier position) :
    signedRelationAction h
        (integrationByPartsRow carrier position) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        integrationByPartsRow
          (exactDimension16DerivativeAlphaReducedAct h carrier) position :=
  integrationByPartsRow_equivariant h carrier position houtermost

example (h : Hypercubic4) (carrier : RelationCarrier)
    (field : Fin carrier.1.1)
    (hsingleton : IsSingletonTrace carrier field) :
    signedRelationAction h (tracelessLetterRow carrier field) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        tracelessLetterRow
          (exactDimension16DerivativeAlphaReducedAct h carrier) field :=
  tracelessLetterRow_equivariant h carrier field hsingleton

#print axioms integrationByPartsRow_equivariant
#print axioms tracelessLetterRow_equivariant

end HypercubicDimension16IBPTraceRelationsRegression
end YangMills
end QuantumTheory
end Mettapedia

