import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticCensus

/-! Positive-stabilizer certificate for quartic representative 3. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicQuarticCensus

open V14HypercubicFDCensus

/-- Every signed hypercubic stabilizer of representative 3 has positive
four-tensor sign. -/
theorem quartic_representative_3_stabilizer_positive :
    ∀ h : Hypercubic4,
      (quarticRepresentative 3).act h = quarticRepresentative 3 →
        (quarticRepresentative 3).tensorSign h = 1 := by
  intro h hstable
  have reflectionCancellation :
      (quarticRepresentative 3).tensorSign h =
        (quarticRepresentative 3).tensorSign (unsignedHypercubic h.perm) := by
    set_option maxRecDepth 10000 in
      cases href0 : h.reflected 0 <;> cases href1 : h.reflected 1 <;>
        cases href2 : h.reflected 2 <;> cases href3 : h.reflected 3 <;>
        simp [quarticRepresentative, quarticRectangleProduct, quarticOfPlanes,
          QuarticMonomial.tensorSign, Sym.ofVector, Sym.toMultiset,
          planeTensorSign,
          SU2LatticeFDCensusNoGo.OrientedPlane.first,
          SU2LatticeFDCensusNoGo.OrientedPlane.second,
          href0, href1, href2, href3]
  rw [reflectionCancellation]
  have unsignedCheck : ∀ permutation : Equiv.Perm Axis,
      (quarticRepresentative 3).act (unsignedHypercubic permutation) =
          quarticRepresentative 3 →
        (quarticRepresentative 3).tensorSign
          (unsignedHypercubic permutation) = 1 := by
    set_option maxRecDepth 10000 in
      decide
  apply unsignedCheck h.perm
  exact (QuarticMonomial.act_eq_unsigned h
    (quarticRepresentative 3)).symm.trans hstable

end V14HypercubicQuarticCensus
end YangMills
end QuantumTheory
end Mettapedia
