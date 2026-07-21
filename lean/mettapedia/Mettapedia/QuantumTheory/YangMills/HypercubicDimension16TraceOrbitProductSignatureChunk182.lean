import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitExecutableSignature
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitProductSignatureData

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitProductSignatureChunk182

open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitExecutableSignature
open HypercubicDimension16TraceOrbitProductSignatureData

def chunkIndex (localIndex : Fin 6) : PositiveRepresentativeIndex :=
  ⟨11648 + localIndex.1, by change 11648 + localIndex.1 < 11654; omega⟩

@[reducible] def expectedProductSignature
    (localIndex : Fin 6) : Nat :=
  (representativeCanonicalProductSignatureCode?
    (chunkIndex localIndex).1).getD 0

/-- Kernel replay of this bounded canonical product-signature range. -/
theorem chunk_product_signatures :
    ∀ localIndex : Fin 6,
      directRepresentativeCanonicalProductSignature (chunkIndex localIndex) =
        expectedProductSignature localIndex := by
  decide +kernel

end HypercubicDimension16TraceOrbitProductSignatureChunk182
end YangMills
end QuantumTheory
end Mettapedia
