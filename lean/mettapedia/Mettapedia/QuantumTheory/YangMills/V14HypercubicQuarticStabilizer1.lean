import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticCensus

/-! Positive-stabilizer certificate for quartic representative 1. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicQuarticCensus

open V14HypercubicFDCensus

/-- Every signed hypercubic stabilizer of representative 1 has positive
four-tensor sign. -/
theorem quartic_representative_1_stabilizer_positive :
    ∀ h : Hypercubic4,
      (quarticRepresentative 1).act h = quarticRepresentative 1 →
        (quarticRepresentative 1).tensorSign h = 1 := by
  intro h _
  rcases planeTensorSign_eq_one_or_neg_one h 4 with hsign4 | hsign4 <;>
    rcases planeTensorSign_eq_one_or_neg_one h 5 with hsign5 | hsign5 <;>
      simp [quarticRepresentative, quarticAdjacentSquares, quarticOfPlanes,
        QuarticMonomial.tensorSign, Sym.ofVector, Sym.toMultiset, hsign4, hsign5]

end V14HypercubicQuarticCensus
end YangMills
end QuantumTheory
end Mettapedia
