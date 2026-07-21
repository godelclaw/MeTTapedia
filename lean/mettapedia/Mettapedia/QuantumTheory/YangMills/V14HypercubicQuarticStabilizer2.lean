import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticCensus

/-! Positive-stabilizer certificate for quartic representative 2. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicQuarticCensus

open V14HypercubicFDCensus

/-- Every signed hypercubic stabilizer of representative 2 has positive
four-tensor sign. -/
theorem quartic_representative_2_stabilizer_positive :
    ∀ h : Hypercubic4,
      (quarticRepresentative 2).act h = quarticRepresentative 2 →
        (quarticRepresentative 2).tensorSign h = 1 := by
  intro h _
  rcases planeTensorSign_eq_one_or_neg_one h 2 with hsign2 | hsign2 <;>
    rcases planeTensorSign_eq_one_or_neg_one h 3 with hsign3 | hsign3 <;>
      simp [quarticRepresentative, quarticOppositeSquares, quarticOfPlanes,
        QuarticMonomial.tensorSign, Sym.ofVector, Sym.toMultiset, hsign2, hsign3]

end V14HypercubicQuarticCensus
end YangMills
end QuantumTheory
end Mettapedia
