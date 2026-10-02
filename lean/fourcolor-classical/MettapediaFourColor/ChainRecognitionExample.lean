import MettapediaFourColor.ChainCoreOccurrence
import MettapediaFourColor.ChainReductionExample
import MettapediaFourColor.ChainFanRecognition

/-! The five-vertex reading in the retained example grows the same complete
source map. All eight boundary vertices are reconstructed by the seam laws. -/

namespace FourColor.ChainRecognitionExample

open ChainCoreReading ChainReductionExample

set_option maxRecDepth 65536

local instance : graph.LocallyFinite := fun v => Subtype.fintype (fun w => graph.Adj v w)

def reading : Reading rotation where
  map := {
    toFun := fun i => NearLinearChainExample.image (i.natAdd 8)
    map_rel' := fun h => NearLinearChainExample.occurrence.map_adj h }
  degree_eq := by decide +kernel
  face := by unfold ExceptionalCoreOrientation.Corner; decide +kernel

theorem induced : ∀ i j, graph.Adj (reading.map i) (reading.map j) → core.Adj i j := by
  decide +kernel

def occurrence : NearLinearChainOccurrence.Occurrence rotation :=
  ChainCoreOccurrence.occurrence reading triangular cyclic induced

/-- The boundary was derived from the core, with no independently chosen
port images. It agrees with the complete retained example. -/
theorem boundary_recovered : ∀ v : Fin 13,
    occurrence.hom v = NearLinearChainExample.image v := by decide +kernel

theorem core_injective : Function.Injective reading.map :=
  ChainCoreReading.injective reading triangular cyclic

def start : graph.Dart := ⟨(39, 28), by decide +kernel⟩

theorem center_degree : graph.degree start.fst = 6 := by decide +kernel

theorem neighbor_word : ∀ n : Fin 4,
    graph.degree (ChainFanRecognition.walk rotation start n.val).snd =
      ChainFanRecognition.word n := by decide +kernel

def fan_reading : Reading rotation :=
  ChainFanRecognition.reading rotation triangular start center_degree neighbor_word

/-- A directed edge and the degree word recover the same five-vertex core. -/
theorem fan_core : ∀ i : Fin 5, fan_reading.map i = reading.map i := by decide +kernel

end FourColor.ChainRecognitionExample
