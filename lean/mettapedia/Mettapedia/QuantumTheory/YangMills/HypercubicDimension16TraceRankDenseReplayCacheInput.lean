import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataRows
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataBasis
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataReplay
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataPartition

/-!
# Bounded decoded input cache for OUR dense trace-rank replay

These lemmas expose selected decoded finite inputs for one fixed dense replay
row.  They are bounded data checks only; they assert neither rank nor a
complete certificate replay.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankCertificateData

set_option maxRecDepth 32768


theorem denseReplay_selectedRow :
    selectedIntegerRow? 11548 = some #[(4486, (1 : Int)), (4553, (-1 : Int)), (8535, (-1 : Int)), (9357, (-1 : Int)), (9458, (1 : Int)), (9466, (1 : Int))] :=
  by
    unfold selectedIntegerRow? selectedIntegerRowsPayload11
    decide +kernel

theorem denseReplay_expectedRow :
    normalizedRationalBasisRow? 11548 = some #[(844, (1 : Int), 2), (1360, (1 : Int), 2), (1363, (-1 : Int), 2), (1422, (1 : Int), 2), (1424, (1 : Int), 1), (1425, (-1 : Int), 1), (1498, (-1 : Int), 1), (1665, (1 : Int), 2), (1668, (1 : Int), 2), (1670, (-1 : Int), 1), (2110, (-1 : Int), 1), (2114, (-1 : Int), 1), (2287, (1 : Int), 1), (2441, (1 : Int), 1), (2442, (-1 : Int), 1), (2445, (1 : Int), 1), (2473, (-1 : Int), 1), (2474, (1 : Int), 1), (2477, (-1 : Int), 1), (2491, (-1 : Int), 1), (2492, (1 : Int), 1), (2493, (-1 : Int), 1), (2522, (1 : Int), 1), (2524, (-1 : Int), 1), (2526, (-1 : Int), 1), (2527, (1 : Int), 1), (2528, (1 : Int), 1), (2530, (1 : Int), 1), (2547, (1 : Int), 1), (2576, (-1 : Int), 1), (2577, (1 : Int), 1), (2578, (-1 : Int), 1), (2580, (-1 : Int), 1), (2581, (1 : Int), 1), (2584, (-1 : Int), 1), (2635, (1 : Int), 1), (2637, (-1 : Int), 1), (2681, (2 : Int), 1), (2682, (-1 : Int), 1), (2683, (-1 : Int), 1), (2730, (2 : Int), 1), (3005, (1 : Int), 1), (3024, (-1 : Int), 1), (3032, (1 : Int), 1), (3056, (-1 : Int), 1), (3701, (-1 : Int), 1), (3824, (1 : Int), 1), (4146, (-1 : Int), 1), (4154, (-1 : Int), 1), (4156, (1 : Int), 1), (4164, (1 : Int), 1), (4192, (-2 : Int), 1), (4193, (1 : Int), 1), (4202, (-1 : Int), 1), (4407, (1 : Int), 1), (4412, (-1 : Int), 1), (4424, (1 : Int), 1), (4486, (-1 : Int), 1), (4558, (1 : Int), 1), (4659, (-1 : Int), 2), (4909, (-2 : Int), 1), (4915, (1 : Int), 1), (4916, (2 : Int), 1), (4965, (1 : Int), 1), (4969, (-1 : Int), 1), (4979, (-1 : Int), 1), (4996, (-1 : Int), 1), (5041, (1 : Int), 1), (5047, (1 : Int), 1), (5053, (-1 : Int), 1), (5054, (-1 : Int), 1), (5108, (2 : Int), 1), (5111, (1 : Int), 1), (5116, (1 : Int), 1), (5117, (1 : Int), 1), (5124, (1 : Int), 1), (5134, (1 : Int), 1), (5135, (1 : Int), 1), (5238, (-1 : Int), 1), (5240, (-2 : Int), 1), (5249, (-2 : Int), 1), (5251, (2 : Int), 1), (5262, (-1 : Int), 1), (5263, (1 : Int), 1), (5314, (1 : Int), 1), (5315, (-1 : Int), 1), (5322, (-1 : Int), 1), (5326, (1 : Int), 1), (5395, (-1 : Int), 1), (5403, (-1 : Int), 1), (5418, (1 : Int), 1), (5420, (-1 : Int), 1), (5789, (-1 : Int), 1), (5790, (-1 : Int), 1), (5793, (-1 : Int), 1), (5878, (1 : Int), 1), (5879, (1 : Int), 1), (5913, (-1 : Int), 1), (6159, (1 : Int), 1), (6239, (-1 : Int), 1), (7803, (-1 : Int), 2), (7804, (1 : Int), 2), (7839, (-1 : Int), 2), (7841, (-1 : Int), 1), (7842, (1 : Int), 1), (7913, (1 : Int), 1), (8071, (-1 : Int), 2), (8074, (-1 : Int), 2), (8076, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload11
    decide +kernel

theorem denseReplay_steps : rationalReplayStepRow? 11548 = some #[10991, 10990, 11039, 11513, 11514, 11540, 7916, 10657, 10656, 8846, 10746, 8848, 8853, 10835, 8956, 11490, 8838, 11544] :=
  by
    unfold rationalReplayStepRow? rationalReplayStepsPayload11
    decide +kernel

theorem denseReplay_targetPivot : pivotColumn? 11548 = some 8076 :=
  by
    unfold pivotColumn? pivotColumnsPayload11
    decide +kernel

theorem denseReplay_targetOwner : columnOwner? 8076 = some 11548 :=
  by
    unfold columnOwner? columnOwnerPayload7
    decide +kernel

#print axioms denseReplay_selectedRow
#print axioms denseReplay_expectedRow
#print axioms denseReplay_steps
#print axioms denseReplay_targetPivot
#print axioms denseReplay_targetOwner

end HypercubicDimension16TraceRankCertificateData
end YangMills
end QuantumTheory
end Mettapedia
