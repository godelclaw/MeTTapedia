import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateCore
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankDenseReplayCacheInput
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankDenseReplayCacheStep0
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankDenseReplayCacheStep1
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankDenseReplayCacheStep2

/-!
# Bounded dense replay for OUR packed trace-rank certificate

The proof composes independently checked decoded inputs for one fixed dense
row.  It does not assert a rank, a conditioning bound, or a complete replay.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankCertificate

open HypercubicDimension16TraceRankCertificateData

set_option maxRecDepth 32768

theorem correctedReplayRow_dense : replaySelectedRow 11548 = true := by
  simp [replaySelectedRow, replayReductionStep,
    denseReplay_selectedRow, denseReplay_expectedRow, denseReplay_steps,
    denseReplay_targetPivot, denseReplay_targetOwner,
    denseReplay_basis_10991, denseReplay_pivot_10991,
    denseReplay_basis_10990, denseReplay_pivot_10990,
    denseReplay_basis_11039, denseReplay_pivot_11039,
    denseReplay_basis_11513, denseReplay_pivot_11513,
    denseReplay_basis_11514, denseReplay_pivot_11514,
    denseReplay_basis_11540, denseReplay_pivot_11540,
    denseReplay_basis_7916, denseReplay_pivot_7916,
    denseReplay_basis_10657, denseReplay_pivot_10657,
    denseReplay_basis_10656, denseReplay_pivot_10656,
    denseReplay_basis_8846, denseReplay_pivot_8846,
    denseReplay_basis_10746, denseReplay_pivot_10746,
    denseReplay_basis_8848, denseReplay_pivot_8848,
    denseReplay_basis_8853, denseReplay_pivot_8853,
    denseReplay_basis_10835, denseReplay_pivot_10835,
    denseReplay_basis_8956, denseReplay_pivot_8956,
    denseReplay_basis_11490, denseReplay_pivot_11490,
    denseReplay_basis_8838, denseReplay_pivot_8838,
    denseReplay_basis_11544, denseReplay_pivot_11544]
  decide +kernel

theorem correctedReplayRange_dense : rationalReplayRangeCheck 11548 1 = true := by
  simp [rationalReplayRangeCheck, correctedReplayRow_dense]

#print axioms correctedReplayRow_dense
#print axioms correctedReplayRange_dense

end HypercubicDimension16TraceRankCertificate
end YangMills
end QuantumTheory
end Mettapedia
