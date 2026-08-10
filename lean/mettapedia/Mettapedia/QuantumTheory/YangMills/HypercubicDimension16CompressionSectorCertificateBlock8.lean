import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionCensus

/-! Kernel-checked class-compressed sector block 8. -/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CompressionCensus

theorem classCompressedSectorCharacter_certificate_block8
    (fieldIndex : Fin 8) :
    classCompressedSectorCharacter 8 (fieldIndex.1 + 1) =
      expectedClassCompressedSectorCharacter 8
        (fieldIndex.1 + 1) := by
  decide +kernel +revert

end HypercubicDimension16CompressionCensus
end YangMills
end QuantumTheory
end Mettapedia
