import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataBasis
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataReplay

/-!
# Bounded decoded step cache 2 for OUR dense trace-rank replay

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
theorem denseReplay_basis_8853 :
    normalizedRationalBasisRow? 8853 = some #[(1425, (1 : Int), 2), (4916, (-1 : Int), 1), (7842, (-1 : Int), 2), (8451, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload8
    decide +kernel

theorem denseReplay_pivot_8853 : pivotColumn? 8853 = some 8451 :=
  by
    unfold pivotColumn? pivotColumnsPayload8
    decide +kernel

theorem denseReplay_basis_10835 :
    normalizedRationalBasisRow? 10835 = some #[(2546, (1 : Int), 1), (4145, (-1 : Int), 1), (5054, (-1 : Int), 1), (8412, (-1 : Int), 1), (8429, (1 : Int), 1), (8432, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload10
    decide +kernel

theorem denseReplay_pivot_10835 : pivotColumn? 10835 = some 8432 :=
  by
    unfold pivotColumn? pivotColumnsPayload10
    decide +kernel

theorem denseReplay_basis_8956 :
    normalizedRationalBasisRow? 8956 = some #[(1451, (1 : Int), 2), (5054, (-1 : Int), 1), (7867, (-1 : Int), 2), (8429, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload8
    decide +kernel

theorem denseReplay_pivot_8956 : pivotColumn? 8956 = some 8429 :=
  by
    unfold pivotColumn? pivotColumnsPayload8
    decide +kernel

theorem denseReplay_basis_11490 :
    normalizedRationalBasisRow? 11490 = some #[(3701, (1 : Int), 1), (4893, (-1 : Int), 1), (5041, (-1 : Int), 1), (8373, (-1 : Int), 1), (8398, (1 : Int), 1), (8400, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload11
    decide +kernel

theorem denseReplay_pivot_11490 : pivotColumn? 11490 = some 8400 :=
  by
    unfold pivotColumn? pivotColumnsPayload11
    decide +kernel

theorem denseReplay_basis_8838 :
    normalizedRationalBasisRow? 8838 = some #[(1422, (1 : Int), 2), (4893, (-1 : Int), 1), (7839, (-1 : Int), 2), (8398, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload8
    decide +kernel

theorem denseReplay_pivot_8838 : pivotColumn? 8838 = some 8398 :=
  by
    unfold pivotColumn? pivotColumnsPayload8
    decide +kernel

theorem denseReplay_basis_11544 :
    normalizedRationalBasisRow? 11544 = some #[(1360, (-1 : Int), 1), (1363, (1 : Int), 1), (1425, (1 : Int), 1), (1451, (-1 : Int), 1), (1670, (1 : Int), 1), (1674, (-1 : Int), 1), (2046, (-1 : Int), 1), (2048, (-1 : Int), 1), (2110, (1 : Int), 1), (2114, (1 : Int), 1), (2442, (2 : Int), 1), (2445, (-2 : Int), 1), (2474, (-2 : Int), 1), (2477, (2 : Int), 1), (2492, (-2 : Int), 1), (2493, (2 : Int), 1), (2522, (-2 : Int), 1), (2524, (2 : Int), 1), (2526, (2 : Int), 1), (2527, (-2 : Int), 1), (2530, (-2 : Int), 1), (2546, (2 : Int), 1), (2547, (-2 : Int), 1), (2576, (2 : Int), 1), (2577, (-2 : Int), 1), (2578, (2 : Int), 1), (2581, (-2 : Int), 1), (2584, (2 : Int), 1), (2635, (-2 : Int), 1), (2637, (2 : Int), 1), (3032, (-2 : Int), 1), (3056, (2 : Int), 1), (4145, (-2 : Int), 1), (4146, (2 : Int), 1), (4154, (2 : Int), 1), (4156, (-2 : Int), 1), (4202, (2 : Int), 1), (4230, (-2 : Int), 1), (4412, (2 : Int), 1), (4424, (-2 : Int), 1), (4915, (-2 : Int), 1), (4916, (-2 : Int), 1), (4965, (-1 : Int), 1), (4969, (3 : Int), 1), (4978, (1 : Int), 1), (4979, (2 : Int), 1), (4983, (1 : Int), 1), (4996, (1 : Int), 1), (4997, (1 : Int), 1), (5053, (2 : Int), 1), (5054, (2 : Int), 1), (5099, (1 : Int), 1), (5108, (-3 : Int), 1), (5116, (-2 : Int), 1), (5117, (-1 : Int), 1), (5124, (-1 : Int), 1), (5134, (-1 : Int), 1), (5135, (-1 : Int), 1), (5314, (-2 : Int), 1), (5315, (2 : Int), 1), (5322, (2 : Int), 1), (5326, (-2 : Int), 1), (5403, (2 : Int), 1), (5418, (-2 : Int), 1), (5748, (-1 : Int), 1), (5750, (-1 : Int), 1), (5752, (-1 : Int), 1), (5789, (1 : Int), 1), (5790, (1 : Int), 1), (5793, (1 : Int), 1), (6239, (1 : Int), 1), (6281, (-1 : Int), 1), (7803, (1 : Int), 1), (7804, (-1 : Int), 1), (7842, (-1 : Int), 1), (7867, (1 : Int), 1), (8076, (-1 : Int), 1), (8080, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload11
    decide +kernel

theorem denseReplay_pivot_11544 : pivotColumn? 11544 = some 8080 :=
  by
    unfold pivotColumn? pivotColumnsPayload11
    decide +kernel

#print axioms denseReplay_basis_8853
#print axioms denseReplay_pivot_8853
#print axioms denseReplay_basis_10835
#print axioms denseReplay_pivot_10835
#print axioms denseReplay_basis_8956
#print axioms denseReplay_pivot_8956
#print axioms denseReplay_basis_11490
#print axioms denseReplay_pivot_11490
#print axioms denseReplay_basis_8838
#print axioms denseReplay_pivot_8838
#print axioms denseReplay_basis_11544
#print axioms denseReplay_pivot_11544
end HypercubicDimension16TraceRankCertificateData
end YangMills
end QuantumTheory
end Mettapedia
