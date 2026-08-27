import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CovariantCommutator

/-! Regression and axiom audit for the cross-sector commutator row. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CovariantCommutatorRegression

open V14HypercubicFDCensus
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16CovariantCommutator

example {count : ℕ} (permutation : Equiv.Perm (Fin count))
    (after : Fin count) :
    insertTraceAfter permutation after after.castSucc = Fin.last count :=
  insertTraceAfter_apply_after permutation after

example {count : ℕ} (permutation : Equiv.Perm (Fin count))
    (before : Fin count) :
    insertTraceBefore permutation before (Fin.last count) =
      before.castSucc :=
  insertTraceBefore_apply_last permutation before

example (h : Hypercubic4) {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier) :
    signedRelationAction h (covariantCommutatorRow site) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        covariantCommutatorRow (site.act h) :=
  covariantCommutatorRow_equivariant h site

#print axioms insertTraceAfter_apply_after
#print axioms insertTraceBefore_apply_last
#print axioms retainedDerivativeOrderEmbedding_mem
#print axioms insertCurvatureCarrier_act
#print axioms insertCurvatureCarrier_tensorSign
#print axioms covariantCommutatorRow_equivariant

end HypercubicDimension16CovariantCommutatorRegression
end YangMills
end QuantumTheory
end Mettapedia

