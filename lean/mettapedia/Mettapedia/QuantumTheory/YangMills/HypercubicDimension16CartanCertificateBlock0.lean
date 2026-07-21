import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanGeneratedData

/-! Kernel-checked dimension-sixteen Cartan certificate block 0. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CartanCensus

theorem canonicalOcticData_valid_block0 :
    ∀ entry : Fin 33,
      let index := octicWitnessBlockIndex 0 (by decide) entry
      octicCode (canonicalOctic index) = canonicalOcticCode index ∧
        (canonicalOcticCertificate index).Valid (canonicalOctic index) ∧
        canonicalOcticIndexOfCode (canonicalOcticCode index) = index := by
  set_option maxRecDepth 100000 in
    intro entry
    fin_cases entry <;> decide

end HypercubicDimension16CartanCensus
end YangMills
end QuantumTheory
end Mettapedia
