import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticWitnessData

/-! Kernel-checked witness block 1 (canonical entries 21 through 41). -/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicQuarticCensus

/-- Every supplied transporter or negative stabilizer in witness block 1
checks against its canonical quartic monomial. -/
theorem canonicalQuarticCertificate_valid_block1 :
    ∀ entry : Fin 21,
      (canonicalQuarticCertificate
          (quarticWitnessBlockIndex 21 (by decide) entry)).Valid
        (canonicalQuartic
          (quarticWitnessBlockIndex 21 (by decide) entry)) := by
  set_option maxRecDepth 10000 in
    intro entry
    fin_cases entry <;> decide

end V14HypercubicQuarticCensus
end YangMills
end QuantumTheory
end Mettapedia
