import MettapediaFourColor.StripDiamondRepair
import MettapediaFourColor.PatchDiskPlanar
import MettapediaFourColor.PatchDiskSources
import MettapediaFourColor.StripPhaseDisk

/-! # Two-stage diamond repair with exterior closure supplied by geometry

The source reading in a spherical triangulation supplies the exterior
closure. Every exterior colouring can then be made compatible with the
restored diamond. The remaining four core vertices are not restored
by this theorem. A previously certified physical disk is a concrete consumer.
-/

namespace FourColor.StripDiamondPhase

open SimpleGraph PatchDisk PatchDisk.Reading PatchDiskSources
open TriangleStripAnchors StripResponseSummary StripSourceExtension KempeBoundarySplit
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation ExceptionalOverlap

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}

/-- There is no restriction to selected initial boundary words and no
separate closure assumption on the exterior. Boundary ports may coincide. -/
theorem from_reading (r : Reading d0099 data)
    (tri : Triangular data) (cyclic : data.IsVertexwiseCyclic)
    (conn : G.Connected) (ambient : (SimpleGraphBridge.rotationHypermap data).Planar)
    (C : (G.induce (keep r)).Coloring Color) :
    ∃ D : (G.induce (keep r)).Coloring Color, ∃ k : DiamondGraph.Coloring Color,
      ∀ i, k (diamondPort i) = D (PatchDisk.Reading.port r i) := by
  let b : Boundary := fun i => C (PatchDisk.Reading.port r i)
  have proper : ProperBoundary b := by
    intro i j edge
    exact C.valid (r.hom.map_rel edge)
  apply compatible _ (PatchDisk.Reading.port r)
    (r.exterior_closed tri cyclic conn ambient) b proper
  exact ⟨C, by simp only [List.map_ofFn, Function.comp_def, b]⟩

/-- An actual coloured disk supplies a nonvacuous geometric consumer. -/
theorem disk_consumer :
    ∃ D : StripPhaseObstruction.exterior.Coloring Color, ∃ k : DiamondGraph.Coloring Color,
      ∀ i, k (diamondPort i) = D (StripPhaseObstruction.ports i) := by
  let b : Boundary := fun i => StripPhaseObstruction.state 0 (StripPhaseObstruction.ports i)
  have proper : ProperBoundary b := by decide +kernel
  apply compatible _ StripPhaseObstruction.ports StripPhaseDisk.closed b proper
  exact ⟨StripPhaseObstruction.state 0, by simp only [List.map_ofFn, Function.comp_def, b]⟩

end
end FourColor.StripDiamondPhase
