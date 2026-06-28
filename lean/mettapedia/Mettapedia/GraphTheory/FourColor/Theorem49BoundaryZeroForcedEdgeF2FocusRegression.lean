import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryZeroForcedEdgeRegression

/-!
Focused F2 no-evader packets for the shared-interior-pair and wheel-with-inner-triangle shells.

The large boundary-zero regression file proves the individual shell thresholds.  This module
exports the detector-facing verdict in the direct form used by the CAP5 path-xor lane: vanishing on
the declared interior controls leaves no nonzero boundary-zero, or boundary-zero plus Kirchhoff,
chain on either focus shell.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace Theorem49BoundaryZeroForcedEdgeF2FocusRegression

open Theorem49BoundaryZeroForcedEdgeRegression

/-- The declared interior controls catch every nonzero F2 evader on both focus shells, both in
the selected-boundary-zero target and in the one-vertex Kirchhoff-repaired target. -/
theorem focusF2_declaredInteriorControls_noEvader_packet :
    (¬ ∃ z : sharedInteriorPairGraph.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding ∧
        z ≠ 0 ∧
          ∀ e ∈ sharedInteriorPairInteriorControlEdges, z e = 0) ∧
      (¬ ∃ z : sharedInteriorPairGraph.edgeSet → Color,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) ∧
          z ≠ 0 ∧
            ∀ e ∈ sharedInteriorPairInteriorControlEdges, z e = 0) ∧
        (¬ ∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
            z ≠ 0 ∧
              ∀ e ∈ wheelWithInnerTriangleInteriorControlEdges, z e = 0) ∧
          (¬ ∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
            z ∈ theorem49BoundaryZeroKirchhoffSubspace
                wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
              z ≠ 0 ∧
                ∀ e ∈ wheelWithInnerTriangleInteriorControlEdges, z e = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨z, hzBoundary, hzNonzero, hvanish⟩
    exact hzNonzero
      (sharedInteriorPair_boundaryZero_controlEdges_interiorEdges hzBoundary (by
        intro e he
        exact hvanish e (by
          simpa [sharedInteriorPairInteriorControlEdges] using he)))
  · rintro ⟨z, hzKirchhoff, hzNonzero, hvanish⟩
    exact hzNonzero
      (sharedInteriorPair_boundaryZeroKirchhoff_controlEdges_interiorEdges hzKirchhoff (by
        intro e he
        exact hvanish e (by
          simpa [sharedInteriorPairInteriorControlEdges] using he)))
  · rintro ⟨z, hzBoundary, hzNonzero, hvanish⟩
    exact hzNonzero
      (wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges hzBoundary (by
        intro e he
        exact hvanish e (by
          simpa [wheelWithInnerTriangleInteriorControlEdges] using he)))
  · rintro ⟨z, hzKirchhoff, hzNonzero, hvanish⟩
    exact hzNonzero
      (wheelWithInnerTriangle_boundaryZeroKirchhoff_controlEdges_interiorEdges hzKirchhoff (by
        intro e he
        exact hvanish e (by
          simpa [wheelWithInnerTriangleInteriorControlEdges] using he)))

end Theorem49BoundaryZeroForcedEdgeF2FocusRegression

end Mettapedia.GraphTheory.FourColor
