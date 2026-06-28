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

/-- Import-facing exact minimum-control packet for the two F2 focus shells.  The finite lab
verdict is: shared-interior-pair needs two controls for boundary-zero and one after the shared
Kirchhoff equation; wheel-with-inner-triangle needs three controls for boundary-zero and two after
the center Kirchhoff equation. -/
theorem focusF2_exactMinimumControlCard_packet :
    (∃ control : Finset sharedInteriorPairGraph.edgeSet,
      control.card = 2 ∧
        ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
          (∀ e ∈ control, z e = 0) →
          z = 0) ∧
    (∀ control : Finset sharedInteriorPairGraph.edgeSet,
      (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        (∀ e ∈ control, z e = 0) →
        z = 0) →
      2 ≤ control.card) ∧
    (∃ control : Finset sharedInteriorPairGraph.edgeSet,
        control.card = 1 ∧
          ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
            z ∈ theorem49BoundaryZeroKirchhoffSubspace
                sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
            (∀ e ∈ control, z e = 0) →
            z = 0) ∧
    (∀ control : Finset sharedInteriorPairGraph.edgeSet,
      (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
        (∀ e ∈ control, z e = 0) →
        z = 0) →
      1 ≤ control.card) ∧
    (∃ control : Finset wheelWithInnerTriangleGraph.edgeSet,
          control.card = 3 ∧
            ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
              z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
              (∀ e ∈ control, z e = 0) →
              z = 0) ∧
    (∀ control : Finset wheelWithInnerTriangleGraph.edgeSet,
      (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        (∀ e ∈ control, z e = 0) →
        z = 0) →
      3 ≤ control.card) ∧
    (∃ control : Finset wheelWithInnerTriangleGraph.edgeSet,
            control.card = 2 ∧
              ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
                z ∈ theorem49BoundaryZeroKirchhoffSubspace
                    wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
                (∀ e ∈ control, z e = 0) →
                z = 0) ∧
    (∀ control : Finset wheelWithInnerTriangleGraph.edgeSet,
      (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
        (∀ e ∈ control, z e = 0) →
        z = 0) →
      2 ≤ control.card) :=
  ⟨sharedInteriorPair_boundaryZero_exactMinimumControlCard.1,
    sharedInteriorPair_boundaryZero_exactMinimumControlCard.2,
    sharedInteriorPair_boundaryZeroKirchhoff_exactMinimumControlCard.1,
    sharedInteriorPair_boundaryZeroKirchhoff_exactMinimumControlCard.2,
    wheelWithInnerTriangle_boundaryZero_exactMinimumControlCard.1,
    wheelWithInnerTriangle_boundaryZero_exactMinimumControlCard.2,
    wheelWithInnerTriangle_boundaryZeroKirchhoff_exactMinimumControlCard.1,
    wheelWithInnerTriangle_boundaryZeroKirchhoff_exactMinimumControlCard.2⟩

/-- Import-facing Kirchhoff-repaired profile packet for the F2 focus shells.  This exposes the
lab rows that are not visible from the declared-control no-evader packet: shared has a no-control
evader but either single interior edge controls it; wheel has single-spoke evaders but every pair
of spokes controls it. -/
theorem focusF2_boundaryZeroKirchhoff_minimalControl_profile_packet :
    (∃ z : sharedInteriorPairGraph.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) ∧
      z ≠ 0) ∧
    (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
      z sip01 = 0 → z = 0) ∧
    (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
      z sip12 = 0 → z = 0) ∧
    (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
      z wit01 = 0 → z wit02 = 0 → z = 0) ∧
    (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
      z wit01 = 0 → z wit03 = 0 → z = 0) ∧
    (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
      z wit02 = 0 → z wit03 = 0 → z = 0) ∧
    (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
      z wit01 = 0 ∧ z ≠ 0) ∧
    (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
      z wit02 = 0 ∧ z ≠ 0) ∧
    (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
      z wit03 = 0 ∧ z ≠ 0) :=
  ⟨sharedInteriorPair_boundaryZeroKirchhoff_minimalControl_profile.1,
    sharedInteriorPair_boundaryZeroKirchhoff_minimalControl_profile.2.1,
    sharedInteriorPair_boundaryZeroKirchhoff_minimalControl_profile.2.2,
    wheelWithInnerTriangle_boundaryZeroKirchhoff_minimalControl_profile.1,
    wheelWithInnerTriangle_boundaryZeroKirchhoff_minimalControl_profile.2.1,
    wheelWithInnerTriangle_boundaryZeroKirchhoff_minimalControl_profile.2.2.1,
    wheelWithInnerTriangle_boundaryZeroKirchhoff_minimalControl_profile.2.2.2.1,
    wheelWithInnerTriangle_boundaryZeroKirchhoff_minimalControl_profile.2.2.2.2.1,
    wheelWithInnerTriangle_boundaryZeroKirchhoff_minimalControl_profile.2.2.2.2.2⟩

end Theorem49BoundaryZeroForcedEdgeF2FocusRegression

end Mettapedia.GraphTheory.FourColor
