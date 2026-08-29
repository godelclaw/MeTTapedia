import KrennX5GaugeNormalizationData
import KrennX5Symmetry

/-! Generated exact witness for the 7776-to-336 X5 orbit cover. -/

namespace Krenn.X5OrbitWitness

open MonochromaticQuantumGraph
open Krenn.X5Symmetry
open Krenn.X5GaugeNormalizationData

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

def casePlaceValue : Fin 5 → Nat := ![1296, 216, 36, 6, 1]

def labelledCaseChoice (case : Fin 7776) : CaseChoice := fun slot =>
  ⟨(case.val / casePlaceValue slot) % 6, Nat.mod_lt _ (by decide)⟩

def representativeLabelledCase (ordinal : Fin 336) : Fin 7776 :=
  ⟨(representativeCase ordinal).val, by omega⟩

def representativeChoice (ordinal : Fin 336) : CaseChoice :=
  labelledCaseChoice (representativeLabelledCase ordinal)

structure OrbitWitness where
  representative : Fin 336
  leaf : LeafSymmetry
  colour : ColourSymmetry
deriving DecidableEq

def defaultOrbitWitness : OrbitWitness := ⟨0, .identity, .p012⟩

theorem representativeChoice_eq_datum_selected : ∀ ordinal slot,
    supportEntry (representativeChoice ordinal) slot =
      (datum ordinal).selected slot := by
  decide

#print axioms Krenn.X5OrbitWitness.representativeChoice_eq_datum_selected

end Krenn.X5OrbitWitness
