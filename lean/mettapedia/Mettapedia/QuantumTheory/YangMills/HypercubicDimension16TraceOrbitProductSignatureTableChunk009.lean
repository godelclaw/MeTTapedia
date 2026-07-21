import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitProductSignatureTable

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitProductSignatureTableChunk009

open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitProductSignatureTable

def chunkIndex (localIndex : Fin 1024) : PositiveRepresentativeIndex :=
  ⟨9216 + localIndex.1, by
    change 9216 + localIndex.1 < 11654
    omega⟩

/-- Bounded replay of the rank inverse and sorted-signature lookup. -/
theorem chunk_rank_tables :
    ∀ localIndex : Fin 1024,
      representativeAtProductSignatureRank
          (productSignatureRank (chunkIndex localIndex)) =
          chunkIndex localIndex ∧
        sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
          expectedProductSignature (chunkIndex localIndex) := by
  decide +kernel

/-- Bounded replay of adjacent strict increase in the sorted table. -/
theorem chunk_sorted_lt :
    ∀ localIndex : Fin 1024,
      sortedProductSignatureAt (9216 + localIndex.1) <
        sortedProductSignatureAt (9216 + localIndex.1 + 1) := by
  decide +kernel

end HypercubicDimension16TraceOrbitProductSignatureTableChunk009
end YangMills
end QuantumTheory
end Mettapedia
