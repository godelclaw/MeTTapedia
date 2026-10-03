import MettapediaFourColor.FourTriangleOccurrence
import MettapediaFourColor.FourTriangleRepair
import MettapediaFourColor.KempeRepairContract
import MettapediaFourColor.CompatibleTraces

/-!
# Strict reconstruction for both complete four-triangle occurrences

A single internal edge provides a nonempty contract for each complete patch.
Its repair follows from full proper-domain rank coverage. Given an actual
occurrence, minimality supplies a colouring after strict two-vertex descent;
planar exterior closure and joint repair reconstruct the ambient colouring.

The complete occurrence retains orientation, core injectivity and separation
from the boundary. Supplying it from the four inner triangles remains separate.
-/

namespace FourColor.FourTriangleRepairGeometry

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open FourTriangleConstruction Hypermap KempeBoundarySplit

set_option maxRecDepth 32768

variable (p : Fin 2)

theorem ring_length : (cfring (config p)).length = 10 := by
  change (cfmap (config p)).cpring.reverse.length = 10
  rw [List.length_reverse]
  have h := congrArg List.length (realization p).ring
  rw [List.length_map, FourTriangleConstruction.cpring] at h
  have size : (ring p).length = 10 := by clear h; revert p; decide +kernel
  exact h.trans size

theorem construction_repair :
    Repairs ((cfmap (config p)).map.RingTrace (cfring (config p)).reverse) 10 :=
  FourTriangleRepair.reference_repair p

theorem reducible {cc : List (cfmap (config p)).Dart}
    (valid : (cfmap (config p)).map.ValidContract (cfring (config p)) cc) :
    (cfmap (config p)).map.CReducible (cfring (config p)) cc := by
  apply KempeRepairContract.reducible_of_repair (embeddable p).base.base.base.cycle valid
  rw [ring_length]
  exact construction_repair p

/-- Both sources use the same labelled first-to-second-core dart. -/
def contractDart : (cfmap (config p)).Dart := (realization p).numbering.symm 62

theorem contract_endpoints :
    (vertex p ((realization p).numbering (contractDart p)),
      vertex p ((realization p).numbering ((cfmap (config p)).map.edge (contractDart p)))) =
        (10, 11) := by
  rw [FourTriangleOccurrence.numbered_edge]
  simp only [contractDart, Equiv.apply_symm_apply]
  revert p; decide +kernel

theorem valid_contract :
    (cfmap (config p)).map.ValidContract (cfring (config p)) [contractDart p] := by
  apply KempeRepairContract.valid_singleton
  · intro h
    have hm := List.mem_map_of_mem (f := (realization p).numbering) h
    rw [FourTriangleOccurrence.numbered_ring] at hm
    have hn : (62 : Fin 70) ∉ (ring p).reverse := by clear h hm; revert p; decide +kernel
    exact hn (by simpa [contractDart] using hm)
  · intro h
    have hm := List.mem_map_of_mem (f := (realization p).numbering) h
    rw [FourTriangleOccurrence.numbered_ring, FourTriangleOccurrence.numbered_edge] at hm
    have hn : (table p).map.edge (62 : Fin 70) ∉ (ring p).reverse := by
      clear h hm; revert p; decide +kernel
    exact hn (by simpa [contractDart] using hm)
  · intro h
    have hn : ¬ (table p).map.CNode (62 : Fin 70) ((table p).map.edge 62) := by
      clear h; revert p; decide +kernel
    apply hn
    have ht := (Hypermap.sameCycle_relabel (realization p).numbering
      (cfmap (config p)).map.node (contractDart p)
        ((cfmap (config p)).map.edge (contractDart p))).mpr h
    change ((cfmap (config p)).map.relabel (realization p).numbering).CNode
      ((realization p).numbering (contractDart p))
      ((realization p).numbering ((cfmap (config p)).map.edge (contractDart p))) at ht
    rw [(realization p).map_eq, FourTriangleOccurrence.numbered_edge] at ht
    simpa [contractDart] using ht

theorem singleton_reducible :
    (cfmap (config p)).map.CReducible (cfring (config p)) [contractDart p] :=
  reducible p (valid_contract p)

noncomputable section

open GoertzelV24TwoEdgeCutMinimality
open MinimalExceptionalEmbedding (graph rotation)

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- Occurrence, initial contract witness and reconstructed colouring belong
 to the same actual ambient map. No exterior augmentation is introduced. -/
theorem colorable (r : FourTriangleOccurrence.Occurrence p
      (rotation original minimal)) :
    (DualGraphQuery.map (rotation original minimal)).FourColorable := by
  classical
  let h := FourTriangleOccurrence.reading p r
  let M := DualGraphQuery.map (rotation original minimal)
  obtain ⟨k, initial⟩ := ActualDualContract.singleton_colorable original minimal
    (embed (cfmap (config p)).map M (cfring (config p)) h (contractDart p))
  exact InjectiveEmbeddedRepair.colorable (embeddable p)
    (ActualDualLocalGeometry.planar original minimal) (DualGraphQuery.plain _)
    (DualGraphQuery.cubic _ (MinimalExceptionalEmbedding.triangular original minimal))
    (FourTriangleOccurrence.preembedding p r (MinimalExceptionalEmbedding.cyclic original minimal))
    (FourTriangleOccurrence.disk_injective p r (MinimalExceptionalEmbedding.cyclic original minimal)
      (MinimalExceptionalEmbedding.triangular original minimal))
    (singleton_reducible p) initial

theorem not_in_minimal (r : FourTriangleOccurrence.Occurrence p
      (rotation original minimal)) : False :=
  ActualDualContract.not_colorable original minimal (colorable p original minimal r)

end
end FourColor.FourTriangleRepairGeometry
