import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataBasis
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataReplay

/-!
# Bounded decoded step cache 1 for OUR dense trace-rank replay

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
theorem denseReplay_basis_7916 :
    normalizedRationalBasisRow? 7916 = some #[(844, (1 : Int), 2), (4230, (-1 : Int), 1), (4659, (-1 : Int), 2), (8685, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload7
    decide +kernel

theorem denseReplay_pivot_7916 : pivotColumn? 7916 = some 8685 :=
  by
    unfold pivotColumn? pivotColumnsPayload7
    decide +kernel

theorem denseReplay_basis_10657 :
    normalizedRationalBasisRow? 10657 = some #[(2441, (1 : Int), 2), (4193, (-1 : Int), 1), (8373, (-1 : Int), 2), (8535, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload10
    decide +kernel

theorem denseReplay_pivot_10657 : pivotColumn? 10657 = some 8535 :=
  by
    unfold pivotColumn? pivotColumnsPayload10
    decide +kernel

theorem denseReplay_basis_10656 :
    normalizedRationalBasisRow? 10656 = some #[(2441, (1 : Int), 2), (4192, (-1 : Int), 1), (8373, (-1 : Int), 2), (8534, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload10
    decide +kernel

theorem denseReplay_pivot_10656 : pivotColumn? 10656 = some 8534 :=
  by
    unfold pivotColumn? pivotColumnsPayload10
    decide +kernel

theorem denseReplay_basis_8846 :
    normalizedRationalBasisRow? 8846 = some #[(1424, (1 : Int), 2), (5047, (-1 : Int), 1), (7841, (-1 : Int), 2), (8515, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload8
    decide +kernel

theorem denseReplay_pivot_8846 : pivotColumn? 8846 = some 8515 :=
  by
    unfold pivotColumn? pivotColumnsPayload8
    decide +kernel

theorem denseReplay_basis_10746 :
    normalizedRationalBasisRow? 10746 = some #[(2491, (1 : Int), 1), (4164, (-1 : Int), 1), (4909, (-1 : Int), 1), (8412, (-1 : Int), 1), (8513, (1 : Int), 1), (8514, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload10
    decide +kernel

theorem denseReplay_pivot_10746 : pivotColumn? 10746 = some 8514 :=
  by
    unfold pivotColumn? pivotColumnsPayload10
    decide +kernel

theorem denseReplay_basis_8848 :
    normalizedRationalBasisRow? 8848 = some #[(1424, (1 : Int), 2), (4909, (-1 : Int), 1), (7841, (-1 : Int), 2), (8513, (1 : Int), 1)] :=
  by
    unfold normalizedRationalBasisRow? normalizedRationalBasisPayload8
    decide +kernel

theorem denseReplay_pivot_8848 : pivotColumn? 8848 = some 8513 :=
  by
    unfold pivotColumn? pivotColumnsPayload8
    decide +kernel

#print axioms denseReplay_basis_7916
#print axioms denseReplay_pivot_7916
#print axioms denseReplay_basis_10657
#print axioms denseReplay_pivot_10657
#print axioms denseReplay_basis_10656
#print axioms denseReplay_pivot_10656
#print axioms denseReplay_basis_8846
#print axioms denseReplay_pivot_8846
#print axioms denseReplay_basis_10746
#print axioms denseReplay_pivot_10746
#print axioms denseReplay_basis_8848
#print axioms denseReplay_pivot_8848
end HypercubicDimension16TraceRankCertificateData
end YangMills
end QuantumTheory
end Mettapedia
