import Mettapedia.GraphTheory.FourColor.CubicCycleIncidence

/-!
# A connected exterior carrier for cycle spokes

In a connected graph, the complement of a vertex set is connected whenever
all its attachment vertices can reach one another in that complement.
For a cubic cycle, these attachment vertices are exactly its named spokes.
A connected outer lobe containing every spoke therefore supplies the
complement hypothesis needed by cycle orientation recognition.
-/

namespace Mettapedia.GraphTheory.FourColor.CycleSpokeConnectivity

open SimpleGraph CubicCycleIncidence

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} {G : SimpleGraph V}

/-- Connectivity of all exterior attachment vertices suffices: every
complementary component must meet an attachment in a connected ambient graph. -/
theorem connected_complement_of_boundary_reachable
    (hconnected : G.Connected) (side : V → Prop)
    (root : V) (hroot : ¬ side root)
    (hboundary : ∀ u v (_hu : side u) (hv : ¬ side v), G.Adj u v →
      (G.induce {v | ¬ side v}).Reachable ⟨root, hroot⟩ ⟨v, hv⟩) :
    (G.induce {v | ¬ side v}).Connected := by
  have along : ∀ {u v} (p : G.Walk u v),
      (∀ hv : ¬ side v, (G.induce {v | ¬ side v}).Reachable ⟨root, hroot⟩ ⟨v, hv⟩) →
      ∀ hu : ¬ side u, (G.induce {v | ¬ side v}).Reachable ⟨root, hroot⟩ ⟨u, hu⟩ := by
    intro u v p
    induction p with
    | nil => exact fun h => h
    | @cons u w v ha p ih =>
        intro hv hu
        by_cases hw : side w
        · exact hboundary w u hw hu ha.symm
        · exact (ih hv hw).trans (SimpleGraph.Adj.reachable
            (G := G.induce {v | ¬ side v}) ha.symm)
  have reaches (v : {v // ¬ side v}) :
      (G.induce {v | ¬ side v}).Reachable ⟨root, hroot⟩ v := by
    obtain ⟨p⟩ := hconnected v.1 root
    exact along p (fun _ => .refl _) v.2
  exact { nonempty := ⟨⟨root, hroot⟩⟩
          preconnected := fun u v => (reaches u).symm.trans (reaches v) }

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite]
  {k : ℕ} [NeZero k] (C : Frame G k)

omit [DecidableRel G.Adj] in
theorem exterior_connected_of_spokes_reachable (hk : 3 ≤ k)
    (hcubic : G.IsRegularOfDegree 3) (hconnected : G.Connected)
    (hspokes : ∀ i, (G.induce {v | ¬ C.keep v}).Reachable
      ⟨C.spoke 0, C.spoke_not_keep 0⟩ ⟨C.spoke i, C.spoke_not_keep i⟩) :
    (G.induce {v | ¬ C.keep v}).Connected := by
  apply connected_complement_of_boundary_reachable hconnected C.keep
    (C.spoke 0) (C.spoke_not_keep 0)
  intro u v hu hv ha
  obtain ⟨i, rfl⟩ := (C.keep_iff u).mp hu
  rcases (C.adjacent_iff hk hcubic i v).mp ha with he | he | he
  · subst v
    exact hspokes i
  · exact (hv (he ▸ C.vertex_keep (i - 1))).elim
  · exact (hv (he ▸ C.vertex_keep (i + 1))).elim

omit [DecidableRel G.Adj] in
/-- All spokes on one connected outer set discharge complement connectivity.
The outer set may contain more vertices than the attachment points. -/
theorem exterior_connected_of_spokes_in_connected_side (hk : 3 ≤ k)
    (hcubic : G.IsRegularOfDegree 3) (hconnected : G.Connected)
    (outer : Set V) (houter : (G.induce outer).Connected)
    (houtside : ∀ v ∈ outer, ¬ C.keep v)
    (hspokes : ∀ i, C.spoke i ∈ outer) :
    (G.induce {v | ¬ C.keep v}).Connected := by
  apply exterior_connected_of_spokes_reachable C hk hcubic hconnected
  intro i
  exact (houter.preconnected ⟨C.spoke 0, hspokes 0⟩ ⟨C.spoke i, hspokes i⟩).map
    (G.induceHomOfLE houtside).toHom

open SimpleGraphDartRotation CycleBoundaryOrientation
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24FaceDualConnectedness GoertzelV24RetainedRegionBoundaryOrder

local instance spokeEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance spokeEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- An actual surrounding connected set supplies the geometry for recognition.
The derived rotation and port return use the same orientation witness. -/
theorem uniform_geometry_of_spokes_in_connected_side
    (rotation : Data G) (hk : 3 ≤ k)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (outer : Set V) (houter : (G.induce outer).Connected)
    (houtside : ∀ v ∈ outer, ¬ C.keep v)
    (hspokes : ∀ i, C.spoke i ∈ outer) :
    ∃ b : Bool,
      (∀ d : CycleBoundaryOrientation.Dart k,
        rotation.vertexRotation (C.star d.1 d.2) =
          C.star (turn k (fun _ => b) d).1 (turn k (fun _ => b) d).2) ∧
      ∀ i, retainedRegionBoundarySuccessor rotation.toRotationSystem C.keep
          (C.boundaryDart rotation i) =
        C.boundaryDart rotation (if b then i + 1 else i - 1) := by
  apply C.uniform_geometry rotation hk hsphere htwo hconnected hrotation
  apply exterior_connected_of_spokes_in_connected_side C hk _ hconnected
    outer houter houtside hspokes
  intro v
  exact (SimpleGraph.degree_instance_independent v _ _).trans
    ((rotation.toRotationSystem_isCubic_iff.mp hsphere.cubic) v)

end
end Mettapedia.GraphTheory.FourColor.CycleSpokeConnectivity
