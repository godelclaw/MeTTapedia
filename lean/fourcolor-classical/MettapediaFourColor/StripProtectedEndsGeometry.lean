import MettapediaFourColor.StripProtectedEndsRepair
import MettapediaFourColor.PatchDiskPlanar
import MettapediaFourColor.PatchDiskSources

/-! # Protected end repair in an actual spherical source reading -/

namespace FourColor.StripProtectedEnds

open SimpleGraph PatchDisk PatchDisk.Reading PatchDiskSources
open TriangleStripAnchors StripResponseSummary StripSourceExtension
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation ExceptionalOverlap

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}

/-- Geometry supplies the exterior closure. The family and protection
conditions are evaluated on the actual exterior boundary colours. -/
theorem from_reading (r : Reading d0099 data)
    (tri : Triangular data) (cyclic : data.IsVertexwiseCyclic)
    (conn : G.Connected) (ambient : (SimpleGraphBridge.rotationHypermap data).Planar)
    (C : (G.induce (keep r)).Coloring Color) (f : Color)
    (family : Family (fun i => C (PatchDisk.Reading.port r i)) f)
    (safe : Safe f (left (fun i => C (PatchDisk.Reading.port r i)))) :
    ∃ D : (G.induce (keep r)).Coloring Color, ∃ k : EndsGraph.Coloring Color,
      ∀ i, k (endPort i) = D (PatchDisk.Reading.port r i) := by
  let b : Boundary := fun i => C (PatchDisk.Reading.port r i)
  have proper : ProperBoundary b := by
    intro i j edge
    exact C.valid (r.hom.map_rel edge)
  apply compatible _ (PatchDisk.Reading.port r)
    (r.exterior_closed tri cyclic conn ambient) b proper f family safe
  exact ⟨C,by simp only [List.map_ofFn,Function.comp_def,b]⟩

end
end FourColor.StripProtectedEnds
