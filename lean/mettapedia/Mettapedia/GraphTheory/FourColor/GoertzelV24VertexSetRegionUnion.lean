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

end GoertzelV24RotationVertexCutProfile

end Mettapedia.GraphTheory.FourColor
