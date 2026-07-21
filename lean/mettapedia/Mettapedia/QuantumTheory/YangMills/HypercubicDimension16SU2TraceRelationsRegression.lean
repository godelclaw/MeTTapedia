import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16SU2TraceRelations

/-! Regression and axiom audit for the `SU(2)` trace relation rows. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16SU2TraceRelationsRegression

open V14HypercubicFDCensus
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16SU2TraceRelations

example {R : Type*} [CommRing R]
    (U A B V : Matrix (Fin 2) (Fin 2) R)
    (hA : Matrix.trace A = 0) (hB : Matrix.trace B = 0) :
    Matrix.trace (U * (A * B) * V) +
        Matrix.trace (U * (B * A) * V) =
      Matrix.trace (A * B) * Matrix.trace (U * V) :=
  traceless_fin_two_trace_anticommutator U A B V hA hB

example {R : Type*} [CommRing R]
    (A B C : Matrix (Fin 2) (Fin 2) R) :
    Matrix.trace A * Matrix.trace B * Matrix.trace C -
        Matrix.trace (A * B) * Matrix.trace C -
        Matrix.trace (A * C) * Matrix.trace B -
        Matrix.trace (B * C) * Matrix.trace A +
        Matrix.trace ((A * B) * C) +
        Matrix.trace ((A * C) * B) = 0 :=
  fin_two_fundamental_trace_identity A B C

example {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) :
    splitAdjacentTraceOrder site site.left = site.right :=
  splitAdjacentTraceOrder_apply_left site

example (h : Hypercubic4) {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) :
    signedRelationAction h (traceAnticommutatorRow site) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        traceAnticommutatorRow (site.act h) :=
  traceAnticommutatorRow_equivariant h site

example (h : Hypercubic4) {carrier : RelationCarrier}
    (site : FundamentalTraceSite carrier) :
    signedRelationAction h (fundamentalTraceRow site) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        fundamentalTraceRow (site.act h) :=
  fundamentalTraceRow_equivariant h site

#print axioms traceless_fin_two_anticommutator
#print axioms traceless_fin_two_trace_anticommutator
#print axioms fin_two_fundamental_trace_identity
#print axioms swapAdjacentTraceOrder_apply_predecessor
#print axioms splitAdjacentTraceOrder_apply_predecessor
#print axioms swapAdjacentTraceCarrier_act
#print axioms splitAdjacentTraceCarrier_tensorSign
#print axioms traceAnticommutatorRow_equivariant
#print axioms fundamentalCycleForward_apply_first
#print axioms fundamentalCycleBackward_apply_third
#print axioms fundamentalTraceRow_equivariant

end HypercubicDimension16SU2TraceRelationsRegression
end YangMills
end QuantumTheory
end Mettapedia
