import Mettapedia.GraphTheory.FourColor.ContourMeshExtraction

/-!
# Original graph walks on the exact rotation-multigraph mesh carrier

The existing adapter identifies primal adjacency with multigraph steps.
Choosing one such edge at each consecutive pair presents any walk as a
`MeshPath`, with exactly the same vertices, including for a closed contour.
No edge is added and no ambient vertex carrier is changed.
-/

namespace Mettapedia.GraphTheory.FourColor.RotationWalkMeshPath

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24MeshIsoperimetry GoertzelV24RotationMultigraphAdapter
open GoertzelV24SimpleGraphFaceDualConnectedness

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

theorem exists_step_edge (data : Data G) {u v : V} (h : G.Adj u v) :
    ∃ e, ((toMultigraph data.toRotationSystem).fst e = u ∧
          (toMultigraph data.toRotationSystem).snd e = v) ∨
         ((toMultigraph data.toRotationSystem).fst e = v ∧
          (toMultigraph data.toRotationSystem).snd e = u) := by
  have hs : (toMultigraph data.toRotationSystem).Step u v :=
    (step_iff_primal_adj data.toRotationSystem u v).mpr (by
      simpa only [rotationPrimalGraph_toRotationSystem_eq] using h)
  obtain ⟨e, _, he⟩ := hs
  exact ⟨e, he⟩

def ofWalk (data : Data G) {u v : V} (p : G.Walk u v) :
    MeshPath (toMultigraph data.toRotationSystem) where
  len := p.length
  vert t := p.getVert t.val
  edge t := (exists_step_edge data (p.adj_getVert_succ t.isLt)).choose
  edge_ends t := (exists_step_edge data (p.adj_getVert_succ t.isLt)).choose_spec

theorem vert_mem_support (data : Data G) {u v : V} (p : G.Walk u v)
    (t : Fin ((ofWalk data p).len + 1)) : (ofWalk data p).vert t ∈ p.support :=
  p.getVert_mem_support t.val

theorem exists_vert_iff (data : Data G) {u v x : V} (p : G.Walk u v) :
    (∃ t, (ofWalk data p).vert t = x) ↔ x ∈ p.support := by
  constructor
  · rintro ⟨t, rfl⟩
    exact vert_mem_support data p t
  · intro hx
    obtain ⟨n, hn, hbound⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    exact ⟨⟨n, by change n < p.length + 1; omega⟩, hn⟩

end
end Mettapedia.GraphTheory.FourColor.RotationWalkMeshPath
