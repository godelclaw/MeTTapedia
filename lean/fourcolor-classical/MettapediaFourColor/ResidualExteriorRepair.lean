import MettapediaFourColor.ResidualExteriorDiskGeometry
import MettapediaFourColor.ResidualExteriorPatch
import MettapediaFourColor.ResidualPortPreparationExample

/-!
# A repaired disk and source compose in the retained ambient graph

The initial exterior trace does not extend directly into the source. Planar
disk geometry supplies joint Kempe closure; the compact seed strategy then
chooses a compatible exterior and source colouring. Their complete boundary
agreement reconstructs the original graph.

This is one seed on one retained occurrence. It does not prove supply of
such occurrences, full D0092 reducibility, or a physical switch-count bound.
-/

namespace FourColor.ResidualExteriorRepair

open SimpleGraph KempeDetachExample KempeBoundarySplit
open FiveTriangleCollapseObstruction ResidualSeedRepairCertificate

theorem ports_order : ports = (List.finRange 11).map ResidualPortPreparation.Example.boundaryPorts := by
  decide +kernel

theorem initial_trace : GraphTrace graph ports seedTrace := by
  refine ⟨ResidualPortPreparation.Example.initial, ?_⟩
  simp only [ports_order, List.map_map, Function.comp_def,
    ResidualPortPreparation.Example.initial_boundary, seedTrace]

/-- Fixing the starting exterior would make reconstruction impossible. -/
theorem initial_cannot_extend : ¬ ∃ K : ambient.Coloring Color,
    ∀ w, K (includeExterior w) = ResidualPortPreparation.Example.initial w := by
  rintro ⟨K, fixed⟩
  let k : upper.graph.Coloring Color := .mk (fun i => K (ResidualExteriorPatch.point i))
    (fun {_ _} edge => K.valid (ResidualExteriorPatch.hom.map_rel edge))
  have boundary (j : Fin 11) :
      k (j.castAdd 7) = ThreeBlockCore.word false false false j := by
    change K (ResidualExteriorPatch.point (j.castAdd 7)) = _
    rw [ResidualExteriorPatch.boundary_reading, fixed]
    exact ResidualPortPreparation.Example.initial_boundary j
  exact (ThreeBlockCore.necessary false false false k boundary).2 rfl

/-- A single source witness agrees with the same exterior at all eleven ports. -/
theorem compatible : ∃ k : upper.graph.Coloring Color, ∃ D : graph.Coloring Color,
    ∀ j : Fin 11, k (j.castAdd 7) = D (ports.get j) := by
  obtain ⟨et, ⟨inside, hins⟩, D, hout⟩ :=
    seed_repair _ ResidualExteriorDisk.closed initial_trace
  obtain ⟨k, agree⟩ := GraphTraceAlignment.align upper.boundary inside
    (ports.map D) (by rw [source_boundary, ports_order]; simp) (hins.symm.trans hout)
  refine ⟨k, D, fun j => ?_⟩
  rw [source_boundary, ports_order, List.map_map, List.map_map] at agree
  exact (List.map_eq_map_iff.mp agree) j (by simp)

/-- All 155 exterior vertices retain the chosen repaired witness when the
seven deleted vertices are filled. No closure or geometry premise remains. -/
theorem reconstructed : ∃ k : upper.graph.Coloring Color,
    ∃ D : graph.Coloring Color, ∃ K : ambient.Coloring Color,
      (∀ i, K (ResidualExteriorPatch.point i) = k i) ∧
      ∀ w, K (includeExterior w) = D w := by
  obtain ⟨k, D, agree⟩ := compatible
  obtain ⟨K, inside, keeps⟩ := ResidualExteriorPatch.reconstruct k D agree
  exact ⟨k, D, K, inside, keeps⟩

end FourColor.ResidualExteriorRepair
