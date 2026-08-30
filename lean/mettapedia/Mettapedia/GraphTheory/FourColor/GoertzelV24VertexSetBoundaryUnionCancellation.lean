import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSetRegionUnion

/-!
# Exact cancellation in the boundary of a union of vertex sides

An edge crossing a union of two vertex sides must cross at least one of the
two sides separately.  If a displayed common seam has both endpoints in the
joined side, every seam edge is absorbed.  The true boundary of the union is
therefore contained in the two old boundaries with the seam deleted.

This is the graph-theoretic serial-composition atom needed by corridor
arguments.  It does not assert that a particular source interface is a
common seam; that remains a geometric obligation of the source realization.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationVertexCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Every true boundary edge of a union crosses at least one of its two
constituent vertex sides.  The converse fails precisely on edges absorbed
between the two sides. -/
theorem vertexSetCrossingEdges_union_subset
    (RS : RotationSystem V E) (left right : Finset V) :
    vertexSetCrossingEdges RS (left ∪ right) ⊆
      vertexSetCrossingEdges RS left ∪ vertexSetCrossingEdges RS right := by
  intro edge hedge
  rw [mem_vertexSetCrossingEdges_iff] at hedge
  rcases hedge with
    ⟨inner, hinnerEndpoint, hinnerUnion,
      outer, houterEndpoint, houterNotUnion⟩
  rcases Finset.mem_union.mp hinnerUnion with hinnerLeft | hinnerRight
  · apply Finset.mem_union_left
    rw [mem_vertexSetCrossingEdges_iff]
    exact ⟨inner, hinnerEndpoint, hinnerLeft,
      outer, houterEndpoint, fun houterLeft =>
        houterNotUnion (Finset.mem_union_left _ houterLeft)⟩
  · apply Finset.mem_union_right
    rw [mem_vertexSetCrossingEdges_iff]
    exact ⟨inner, hinnerEndpoint, hinnerRight,
      outer, houterEndpoint, fun houterRight =>
        houterNotUnion (Finset.mem_union_right _ houterRight)⟩

/-- If every edge of a named seam has both endpoints in the joined vertex
side, then the seam is disjoint from the joined side's true frontier. -/
theorem seam_disjoint_vertexSetCrossingEdges_union_of_endpoints_subset
    (RS : RotationSystem V E) (left right : Finset V) (seam : Finset E)
    (hseam : ∀ edge ∈ seam, RS.endpoints edge ⊆ left ∪ right) :
    Disjoint seam (vertexSetCrossingEdges RS (left ∪ right)) := by
  rw [Finset.disjoint_left]
  intro edge hedgeSeam hedgeCrossing
  exact (not_mem_vertexSetCrossingEdges_of_endpoints_subset RS
    (left ∪ right) edge (hseam edge hedgeSeam)) hedgeCrossing

/-- Exact serial-boundary upper bound.  Once a common seam is absorbed, a
new boundary edge can only be an old boundary edge away from that seam. -/
theorem vertexSetCrossingEdges_union_subset_sdiff_union_sdiff
    (RS : RotationSystem V E) (left right : Finset V) (seam : Finset E)
    (habsorbed :
      Disjoint seam (vertexSetCrossingEdges RS (left ∪ right))) :
    vertexSetCrossingEdges RS (left ∪ right) ⊆
      (vertexSetCrossingEdges RS left \ seam) ∪
        (vertexSetCrossingEdges RS right \ seam) := by
  intro edge hedge
  have hcandidates := vertexSetCrossingEdges_union_subset RS left right hedge
  have hnotSeam : edge ∉ seam := by
    exact fun hedgeSeam => Finset.disjoint_left.mp habsorbed hedgeSeam hedge
  rcases Finset.mem_union.mp hcandidates with hleft | hright
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hleft, hnotSeam⟩)
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hright, hnotSeam⟩)

/-- Endpoint absorption is a sufficient, directly checkable premise for the
serial-boundary upper bound. -/
theorem vertexSetCrossingEdges_union_subset_sdiff_union_sdiff_of_endpoints
    (RS : RotationSystem V E) (left right : Finset V) (seam : Finset E)
    (hseam : ∀ edge ∈ seam, RS.endpoints edge ⊆ left ∪ right) :
    vertexSetCrossingEdges RS (left ∪ right) ⊆
      (vertexSetCrossingEdges RS left \ seam) ∪
        (vertexSetCrossingEdges RS right \ seam) := by
  exact vertexSetCrossingEdges_union_subset_sdiff_union_sdiff RS left right
    seam
    (seam_disjoint_vertexSetCrossingEdges_union_of_endpoints_subset RS left
      right seam hseam)

end

end GoertzelV24RotationVertexCutProfile

end Mettapedia.GraphTheory.FourColor
