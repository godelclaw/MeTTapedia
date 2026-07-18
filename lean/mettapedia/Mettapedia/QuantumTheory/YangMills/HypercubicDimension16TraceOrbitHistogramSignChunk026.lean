import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramExecutable

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitHistogramSignChunk026

open HypercubicRawFDCharacterCensus
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitExecutableSignature
open HypercubicDimension16TraceOrbitHistogramExecutable

def chunkIndex (localIndex : Fin 256) : PositiveRepresentativeIndex :=
  ⟨6656 + localIndex.1, by change 6656 + localIndex.1 < 11654; omega⟩

/-- Every pure reflection has positive tensor sign in this range. -/
theorem chunk_reflection_signs_positive :
    ∀ localIndex : Fin 256, ∀ reflection : Fin 16,
      directRepresentativeTensorSign (chunkIndex localIndex)
          (decodedHypercubicCharacterElement 0 reflection) = 1 := by
  decide +kernel

/-- Every unsigned plane-histogram stabilizer has positive sign in this range. -/
theorem chunk_unsigned_histogram_stabilizers_positive :
    ∀ localIndex : Fin 256, ∀ permutation : Fin 24,
      directRepresentativePlaneHistogramAt (chunkIndex localIndex)
          (decodedHypercubicCharacterElement permutation 0) =
        directRepresentativePlaneHistogramAt (chunkIndex localIndex) 1 →
      directRepresentativeTensorSign (chunkIndex localIndex)
          (decodedHypercubicCharacterElement permutation 0) = 1 := by
  decide +kernel

end HypercubicDimension16TraceOrbitHistogramSignChunk026
end YangMills
end QuantumTheory
end Mettapedia
