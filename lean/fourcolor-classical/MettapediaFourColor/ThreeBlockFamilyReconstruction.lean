import MettapediaFourColor.ThreeBlockExteriorPlanar
import MettapediaFourColor.ThreeBlockRepairTransfer

/-! # Reconstruct all eight three-run choices in the actual ambient map

The actual induced exterior supplies its entire Kempe-closed joint trace
relation. The shared repair changes that exterior if necessary, aligns the
source colouring at every boundary port, and fills all seven core vertices.
Occurrence supply and boundary words outside this family remain separate.
-/

namespace FourColor.ThreeBlockDiskBoundary

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalOverlap KempeBoundarySplit FiveTriangleCollapseObstruction

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}
  (r : Reading data) (tri : Triangular data) (cyclic : data.IsVertexwiseCyclic)
  (conn : G.Connected) (ambient : (SimpleGraphBridge.rotationHypermap data).Planar)

include tri cyclic conn ambient

theorem repair_of_boundary_trace (C : (G.induce (keep r)).Coloring Color)
    (repairable : KempeCoclosure ThreeBlockRepairTransfer.Supports
      (trace ((List.finRange 11).map (fun j => C (port r j))))) :
    ∃ D : (G.induce (keep r)).Coloring Color, ∃ K : G.Coloring Color,
      ∀ w, K w.val = D w := by
  have closed := exterior_closed r tri cyclic conn ambient
  have start : GraphTrace (G.induce (keep r)) ((List.finRange 11).map (port r))
      (trace ((List.finRange 11).map (fun j => C (port r j)))) := by
    exact ⟨C, by simp only [List.map_map, Function.comp_def]⟩
  obtain ⟨et, ⟨inside, hins⟩, D, hout⟩ := repairable _ closed start
  have ht : trace (upper.boundary.map inside) =
      trace ((List.finRange 11).map (fun j => D (port r j))) := by
    simpa only [List.map_map, Function.comp_def] using hins.symm.trans hout
  obtain ⟨k, agree⟩ := GraphTraceAlignment.align upper.boundary inside
    ((List.finRange 11).map (fun j => D (port r j)))
    (by simp [ResidualSeedRepairCertificate.source_boundary]) ht
  have boundary (j : Fin 11) : k (j.castAdd 7) = D (port r j) := by
    rw [ResidualSeedRepairCertificate.source_boundary, List.map_map] at agree
    exact (List.map_eq_map_iff.mp agree) j (by simp)
  obtain ⟨K, he, _⟩ := (exteriorReading r tri).reconstruct
    (exterior_covers r tri) (core_stars r cyclic) D k boundary
  exact ⟨D, K, he⟩

/-- The same geometric occurrence and shared repair handle every joint choice
in the symbolic three-run family. The initial exterior need not extend. -/
theorem repair_three_run (a b c : Bool) (C : (G.induce (keep r)).Coloring Color)
    (initial : ∀ j, C (port r j) = ThreeBlockCore.word a b c j) :
    ∃ D : (G.induce (keep r)).Coloring Color, ∃ K : G.Coloring Color,
      ∀ w, K w.val = D w := by
  apply repair_of_boundary_trace r tri cyclic conn ambient C
  simpa only [initial, ThreeBlockRepairTransfer.threeTrace]
    using ThreeBlockRepairTransfer.three_run_repair a b c

end
end FourColor.ThreeBlockDiskBoundary
