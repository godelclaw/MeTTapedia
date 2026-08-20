import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataRows
import Mathlib

/-!
# Kernel-reduction regressions for OUR packed trace-rank data

These two checks exercise the first and final rows of a 1024-row page.  They
are representation checks only: they do not assert rank, conditioning, or a
complete relation census.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankCertificateData

set_option maxRecDepth 1000000

open HypercubicDimension16PackedFiniteDataCodec

theorem selectedIntegerRow_packed_first_regression :
    selectedIntegerRow? 0 = some #[(0, (1 : Int))] := by
  unfold selectedIntegerRow? selectedIntegerRowsPayload0
  norm_num [decodeCountPrefixedPackedNatChunks, decodePackedNatChunkValuesLoop,
    packedNatChunkField, packedNatField, decodeIntegerSparseRow]

theorem selectedIntegerRow_packed_page_end_regression :
    selectedIntegerRow? 1023 = some #[(1023, (1 : Int))] := by
  unfold selectedIntegerRow? selectedIntegerRowsPayload0
  norm_num [decodeCountPrefixedPackedNatChunks, decodePackedNatChunkValuesLoop,
    packedNatChunkField, packedNatField, decodeIntegerSparseRow]

end HypercubicDimension16TraceRankCertificateData

end YangMills
end QuantumTheory
end Mettapedia
