import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCensus

/-! Positive-stabilizer certificate for dimension-sixteen representative 1. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CartanCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem octic_representative_1_stabilizer_positive :
    ∀ h : Hypercubic4,
      (octicRepresentative 1).act h = octicRepresentative 1 →
        (octicRepresentative 1).tensorSign h = 1 := by
  intro h hstable
  have reflectionCancellation :
      (octicRepresentative 1).tensorSign h =
        (octicRepresentative 1).tensorSign
          (unsignedHypercubic h.perm) := by
    set_option maxRecDepth 100000 in
      cases href0 : h.reflected 0 <;> cases href1 : h.reflected 1 <;>
        cases href2 : h.reflected 2 <;> cases href3 : h.reflected 3 <;>
        simp [octicRepresentative, octicOfPlanes,
          OcticMonomial.tensorSign, Sym.ofVector, Sym.toMultiset,
          planeTensorSign,
          SU2LatticeFDCensusNoGo.OrientedPlane.first,
          SU2LatticeFDCensusNoGo.OrientedPlane.second,
          href0, href1, href2, href3]
  rw [reflectionCancellation]
  have unsignedCheck : ∀ permutation : Equiv.Perm Axis,
      (octicRepresentative 1).act
          (unsignedHypercubic permutation) = octicRepresentative 1 →
        (octicRepresentative 1).tensorSign
          (unsignedHypercubic permutation) = 1 := by
    set_option maxRecDepth 100000 in decide
  apply unsignedCheck h.perm
  exact (OcticMonomial.act_eq_unsigned h
    (octicRepresentative 1)).symm.trans hstable

end HypercubicDimension16CartanCensus
end YangMills
end QuantumTheory
end Mettapedia
