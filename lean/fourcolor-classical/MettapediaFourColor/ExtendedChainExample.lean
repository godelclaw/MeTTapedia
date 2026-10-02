import MettapediaFourColor.ActualExtendedChainReduction
import MettapediaFourColor.ChainBoundaryGeometry

/-! A second complete fan profile in the retained finite triangulation.
Its whole nine-port interface is computed from the same four-neighbour
walk used by the general actual-map recognition theorem. -/

namespace FourColor.ExtendedChainExample

open ChainBoundaryExample
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation

set_option maxRecDepth 65536

def start : graph.Dart := ⟨(48, 117), by decide +kernel⟩

theorem center_degree : graph.degree start.fst = 6 := by decide +kernel

theorem neighbor_word : ∀ n : Fin 4,
    graph.degree (ChainFanRecognition.walk rotation start n.val).snd =
      ExtendedChainCore.word n := by decide +kernel

def reading : ExtendedChainCore.Reading rotation :=
  ExtendedChainCore.of_word triangular start center_degree neighbor_word

theorem core_images : ∀ i : Fin 5,
    reading.map i = (![1, 48, 118, 17, 117] : Fin 5 → Fin 162) i := by decide +kernel

theorem induced : ∀ i j, graph.Adj (reading.map i) (reading.map j) →
    ThreeTriangleFan.core.Adj i j := by decide +kernel

def occurrence : ExtendedChainOccurrence.Occurrence rotation :=
  ExtendedChainRecognition.occurrence reading triangular cyclic induced

theorem complete_images : ∀ v : Fin 14, ExtendedChainCompletion.vertex reading v =
    (![47, 51, 125, 120, 52, 119, 123, 50, 49, 17, 117, 48, 118, 1] :
      Fin 14 → Fin 162) v := by decide +kernel

theorem complete_near (v : Fin 14) :
    ExtendedChainCompletion.vertex reading v ∈ LocalCoverageAssembly.closedBall graph 48 2 :=
  ExtendedChainCompletion.vertex_near reading v

end FourColor.ExtendedChainExample
