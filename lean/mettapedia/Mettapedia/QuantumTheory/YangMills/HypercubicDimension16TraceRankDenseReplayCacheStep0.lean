import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataBasis
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataReplay

/-!
# Bounded decoded step cache 0 for OUR dense trace-rank replay

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
theorem denseReplay_basis_10991 :
    normalizedRationalBasisRow? 10991 = some #[(2683, (1 : Int), 1), (4558, (-1 : Int), 1), (5263, (-1 : Int), 1), (8515, (-1 : Int), 1), (9459, (1 : Int), 1), (9466, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload10
    decide +kernel

theorem denseReplay_pivot_10991 : pivotColumn? 10991 = some 9466 :=
  by
    unfold pivotColumn? pivotColumnsPayload10
    decide +kernel

theorem denseReplay_basis_10990 :
    normalizedRationalBasisRow? 10990 = some #[(2682, (1 : Int), 1), (4553, (-1 : Int), 1), (5262, (-1 : Int), 1), (8514, (-1 : Int), 1), (9458, (1 : Int), 1), (9459, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload10
    decide +kernel

theorem denseReplay_pivot_10990 : pivotColumn? 10990 = some 9459 :=
  by
    unfold pivotColumn? pivotColumnsPayload10
    decide +kernel

theorem denseReplay_basis_11039 :
    normalizedRationalBasisRow? 11039 = some #[(1498, (-1 : Int), 2), (2681, (1 : Int), 1), (2683, (-1 : Int), 1), (2730, (1 : Int), 1), (4553, (-1 : Int), 1), (4558, (1 : Int), 1), (5240, (-1 : Int), 1), (5249, (-1 : Int), 1), (5251, (1 : Int), 1), (5262, (-1 : Int), 1), (5263, (1 : Int), 1), (7913, (1 : Int), 2), (8513, (-1 : Int), 1), (8515, (1 : Int), 1), (8534, (-1 : Int), 1), (9458, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload10
    decide +kernel

theorem denseReplay_pivot_11039 : pivotColumn? 11039 = some 9458 :=
  by
    unfold pivotColumn? pivotColumnsPayload10
    decide +kernel

theorem denseReplay_basis_11513 :
    normalizedRationalBasisRow? 11513 = some #[(1670, (1 : Int), 1), (2110, (1 : Int), 1), (2114, (1 : Int), 1), (3032, (-2 : Int), 1), (3824, (-1 : Int), 1), (5099, (-1 : Int), 1), (5108, (-1 : Int), 1), (5117, (-1 : Int), 1), (5124, (-1 : Int), 1), (5134, (-1 : Int), 1), (5135, (-1 : Int), 1), (5789, (1 : Int), 1), (5790, (1 : Int), 1), (5793, (1 : Int), 1), (6239, (1 : Int), 1), (8076, (-1 : Int), 1), (8712, (2 : Int), 1), (9357, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload11
    decide +kernel

theorem denseReplay_pivot_11513 : pivotColumn? 11513 = some 9357 :=
  by
    unfold pivotColumn? pivotColumnsPayload11
    decide +kernel

theorem denseReplay_basis_11514 :
    normalizedRationalBasisRow? 11514 = some #[(1665, (1 : Int), 4), (1668, (1 : Int), 4), (1670, (1 : Int), 4), (1674, (-1 : Int), 4), (2046, (-1 : Int), 4), (2048, (-1 : Int), 4), (2110, (1 : Int), 4), (2114, (1 : Int), 4), (2287, (1 : Int), 2), (3005, (1 : Int), 2), (3024, (-1 : Int), 2), (3032, (-1 : Int), 1), (4965, (1 : Int), 4), (4969, (1 : Int), 4), (4978, (1 : Int), 4), (4983, (1 : Int), 4), (4996, (1 : Int), 4), (4997, (1 : Int), 4), (5099, (-1 : Int), 4), (5108, (-1 : Int), 4), (5117, (-1 : Int), 4), (5124, (-1 : Int), 4), (5134, (-1 : Int), 4), (5135, (-1 : Int), 4), (5238, (-1 : Int), 2), (5395, (-1 : Int), 2), (5420, (-1 : Int), 2), (5748, (-1 : Int), 4), (5750, (-1 : Int), 4), (5752, (-1 : Int), 4), (5789, (1 : Int), 4), (5790, (1 : Int), 4), (5793, (1 : Int), 4), (5878, (1 : Int), 2), (5879, (1 : Int), 2), (5913, (-1 : Int), 2), (6159, (1 : Int), 2), (6239, (1 : Int), 4), (6281, (-1 : Int), 4), (8071, (-1 : Int), 4), (8074, (-1 : Int), 4), (8076, (-1 : Int), 4), (8080, (1 : Int), 4), (8685, (-1 : Int), 2), (8704, (1 : Int), 2), (8712, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload11
    decide +kernel

theorem denseReplay_pivot_11514 : pivotColumn? 11514 = some 8712 :=
  by
    unfold pivotColumn? pivotColumnsPayload11
    decide +kernel

theorem denseReplay_basis_11540 :
    normalizedRationalBasisRow? 11540 = some #[(2473, (1 : Int), 1), (2528, (-1 : Int), 1), (2580, (1 : Int), 1), (4192, (-1 : Int), 1), (4407, (-1 : Int), 1), (4996, (1 : Int), 1), (5111, (-1 : Int), 1), (8400, (-1 : Int), 1), (8432, (1 : Int), 1), (8451, (-1 : Int), 1), (8534, (1 : Int), 1), (8704, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload11
    decide +kernel

theorem denseReplay_pivot_11540 : pivotColumn? 11540 = some 8704 :=
  by
    unfold pivotColumn? pivotColumnsPayload11
    decide +kernel

#print axioms denseReplay_basis_10991
#print axioms denseReplay_pivot_10991
#print axioms denseReplay_basis_10990
#print axioms denseReplay_pivot_10990
#print axioms denseReplay_basis_11039
#print axioms denseReplay_pivot_11039
#print axioms denseReplay_basis_11513
#print axioms denseReplay_pivot_11513
#print axioms denseReplay_basis_11514
#print axioms denseReplay_pivot_11514
#print axioms denseReplay_basis_11540
#print axioms denseReplay_pivot_11540
end HypercubicDimension16TraceRankCertificateData
end YangMills
end QuantumTheory
end Mettapedia
