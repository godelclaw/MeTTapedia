import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer0
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer1
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer2
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer3
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer4
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer5
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer6
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer7
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer8
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer9
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer10
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer11
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer12
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer13
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer14
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer15
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer16
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificate

/-! # Positive stabilizers for all seventeen dimension-sixteen representatives -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CartanCensus

open V14HypercubicFDCensus

theorem octic_representative_stabilizer_positive :
    ∀ coordinate : Fin 17, ∀ h : Hypercubic4,
      (octicRepresentative coordinate).act h =
          octicRepresentative coordinate →
        (octicRepresentative coordinate).tensorSign h = 1 := by
  intro coordinate
  fin_cases coordinate
  · exact octic_representative_0_stabilizer_positive
  · exact octic_representative_1_stabilizer_positive
  · exact octic_representative_2_stabilizer_positive
  · exact octic_representative_3_stabilizer_positive
  · exact octic_representative_4_stabilizer_positive
  · exact octic_representative_5_stabilizer_positive
  · exact octic_representative_6_stabilizer_positive
  · exact octic_representative_7_stabilizer_positive
  · exact octic_representative_8_stabilizer_positive
  · exact octic_representative_9_stabilizer_positive
  · exact octic_representative_10_stabilizer_positive
  · exact octic_representative_11_stabilizer_positive
  · exact octic_representative_12_stabilizer_positive
  · exact octic_representative_13_stabilizer_positive
  · exact octic_representative_14_stabilizer_positive
  · exact octic_representative_15_stabilizer_positive
  · exact octic_representative_16_stabilizer_positive

end HypercubicDimension16CartanCensus
end YangMills
end QuantumTheory
end Mettapedia
