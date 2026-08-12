import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationVertexCutProfile

/-!
# Vertex-side regions commute with finite unions

The regional edge carrier induced by a union of vertex sides is exactly the
union of the carriers induced by the individual sides.  This elementary fact
is useful when a compositional corridor prefix is presented as a union of
literal vertex-side Cells: it recovers one honest vertex-side carrier before
any claim is made about that carrier's boundary.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationVertexCutProfile

variable {V E I : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- The regional edge construction distributes over a finite union of
vertex sides. -/
theorem vertexSetRegionEdges_biUnion
    (RS : RotationSystem V E) (indices : Finset I)
    (side : I → Finset V) :
    indices.biUnion (fun index => vertexSetRegionEdges RS (side index)) =
      vertexSetRegionEdges RS (indices.biUnion side) := by
  ext edge
  simp only [Finset.mem_biUnion, mem_vertexSetRegionEdges_iff,
    edgeMeetsVertexSet]
  constructor
  · rintro ⟨index, hindex, vertex, hvertexEndpoint, hvertexSide⟩
    exact ⟨vertex, hvertexEndpoint, index, hindex, hvertexSide⟩
  · rintro ⟨vertex, hvertexEndpoint, index, hindex, hvertexSide⟩
    exact ⟨index, hindex, vertex, hvertexEndpoint, hvertexSide⟩

/-- Every edge crossing a finite union of vertex sides crosses at least one
of the constituent sides.  The reverse inclusion need not hold: an edge
between two constituent sides is internal after the union is formed. -/
theorem vertexSetCrossingEdges_biUnion_subset
    (RS : RotationSystem V E) (indices : Finset I)
    (side : I → Finset V) :
    vertexSetCrossingEdges RS (indices.biUnion side) ⊆
      indices.biUnion (fun index => vertexSetCrossingEdges RS (side index)) := by
  intro edge hedge
  rw [mem_vertexSetCrossingEdges_iff] at hedge
  rcases hedge with
    ⟨inner, hinnerEndpoint, hinnerUnion,
      outer, houterEndpoint, houterNotUnion⟩
  rcases Finset.mem_biUnion.mp hinnerUnion with
    ⟨index, hindex, hinnerSide⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨index, hindex, ?_⟩
  rw [mem_vertexSetCrossingEdges_iff]
  refine ⟨inner, hinnerEndpoint, hinnerSide,
    outer, houterEndpoint, ?_⟩
  intro houterSide
  exact houterNotUnion (Finset.mem_biUnion.mpr
    ⟨index, hindex, houterSide⟩)

end GoertzelV24RotationVertexCutProfile

end Mettapedia.GraphTheory.FourColor
