import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticCensus

/-! Positive-stabilizer certificate for quartic representative 0. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicQuarticCensus

open V14HypercubicFDCensus

/-- Every signed hypercubic stabilizer of representative 0 has positive
four-tensor sign. -/
theorem quartic_representative_0_stabilizer_positive :
    ∀ h : Hypercubic4,
      (quarticRepresentative 0).act h = quarticRepresentative 0 →
        (quarticRepresentative 0).tensorSign h = 1 := by
  intro h _
  rcases planeTensorSign_eq_one_or_neg_one h 5 with hsign | hsign <;>
    simp [quarticRepresentative, quarticPureFourth, quarticOfPlanes,
      QuarticMonomial.tensorSign, Sym.ofVector, Sym.toMultiset, hsign]

end V14HypercubicQuarticCensus
end YangMills
end QuantumTheory
end Mettapedia
