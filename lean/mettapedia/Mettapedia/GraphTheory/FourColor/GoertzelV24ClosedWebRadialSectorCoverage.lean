import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialLength

/-!
# Ambient coverage by the two singleton-pair radial paths

At the good five-stub boundary, the current Fable manuscript describes the
singleton colour-pair graph as two radial paths jointly covering every
internal vertex.  `RadialPathPair.cover_support` already records the
support-side statement.  This module transports it to the ambient graph.

This is an L8-to-L6 input, not a sector-separation theorem.  In particular,
it does not manufacture a complementary vertex side, a simple transversal,
or a splice boundary.  Those remain rotation-system geometry.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebRadialSectorCoverage

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebRadialPathChordDiagram
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24ClosedWebRadialLength

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- Forgetting the selected-colour support subtype preserves membership in
the ambient radial path. -/
theorem mem_ambientRadialPath_verts_of_mem_componentPath_verts
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    {vertex : ColorPairSupportVertex C first second}
    (hvertex : vertex ∈ radial.path.toSubgraph.verts) :
    vertex.1 ∈ (ambientRadialPath radial).toSubgraph.verts := by
  rw [SimpleGraph.Walk.mem_verts_toSubgraph] at hvertex ⊢
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvertex with
    ⟨position, hposition, _⟩
  rw [← hposition, ← ambientRadialPath_getVert radial]
  exact (ambientRadialPath radial).getVert_mem_support position

/-- The source's two radial paths cover every interior vertex in the ambient
closed-web graph.  This is the graph-level form of `cover_support`; it does
not identify the complementary sectors cut by the two paths. -/
theorem interior_vertex_mem_ambientRadialPath_union
    {data : AnnularBoundaryData G outerCount}
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    (pair : RadialPathPair data C first second)
    {vertex : V} (hinterior : vertex ∈ data.interiorVertices) :
    vertex ∈ (ambientRadialPath pair.firstPath).toSubgraph.verts ∨
      vertex ∈ (ambientRadialPath pair.secondPath).toSubgraph.verts := by
  let supportVertex : ColorPairSupportVertex C first second :=
    interiorSupportVertex data hdata C hC hpair ⟨vertex, hinterior⟩
  have hcover : supportVertex ∈ pair.firstPath.path.toSubgraph.verts ∪
      pair.secondPath.path.toSubgraph.verts := by
    rw [pair.cover_support]
    exact Set.mem_univ supportVertex
  rcases hcover with hfirst | hsecond
  · exact Or.inl
      (mem_ambientRadialPath_verts_of_mem_componentPath_verts
        pair.firstPath hfirst)
  · exact Or.inr
      (mem_ambientRadialPath_verts_of_mem_componentPath_verts
        pair.secondPath hsecond)

/-- Any proposed sector lying off both radial paths is free of interior
vertices.  A later rotation-system separation theorem need only establish the
displayed disjointness to inherit the source's ``empty sector interior''
conclusion. -/
theorem disjoint_interiorVertices_of_disjoint_ambientRadialPaths
    {data : AnnularBoundaryData G outerCount}
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    (pair : RadialPathPair data C first second)
    (side : Set V)
    (hside : Disjoint side
      ((ambientRadialPath pair.firstPath).toSubgraph.verts ∪
        (ambientRadialPath pair.secondPath).toSubgraph.verts)) :
    Disjoint side ↑data.interiorVertices := by
  rw [Set.disjoint_left]
  intro vertex hvertexSide hvertexInterior
  rcases interior_vertex_mem_ambientRadialPath_union
      hdata C hC hpair pair hvertexInterior with hfirst | hsecond
  · exact (Set.disjoint_left.1 hside) hvertexSide (Or.inl hfirst)
  · exact (Set.disjoint_left.1 hside) hvertexSide (Or.inr hsecond)

end

end GoertzelV24ClosedWebRadialSectorCoverage

end Mettapedia.GraphTheory.FourColor
