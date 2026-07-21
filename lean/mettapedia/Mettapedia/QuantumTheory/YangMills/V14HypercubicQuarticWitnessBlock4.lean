import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticWitnessData

/-! Kernel-checked witness block 4 (canonical entries 84 through 104). -/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicQuarticCensus

/-- Every supplied transporter or negative stabilizer in witness block 4
checks against its canonical quartic monomial. -/
theorem canonicalQuarticCertificate_valid_block4 :
    ∀ entry : Fin 21,
      (canonicalQuarticCertificate
          (quarticWitnessBlockIndex 84 (by decide) entry)).Valid
        (canonicalQuartic
          (quarticWitnessBlockIndex 84 (by decide) entry)) := by
  set_option maxRecDepth 10000 in
    intro entry
    fin_cases entry <;> decide

end V14HypercubicQuarticCensus
end YangMills
end QuantumTheory
end Mettapedia
