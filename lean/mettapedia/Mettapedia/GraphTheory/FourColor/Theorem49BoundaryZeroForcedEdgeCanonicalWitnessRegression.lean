import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryZeroForcedEdgeRegression
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusWitness

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49BoundaryZeroForcedEdgeRegression

/-!
This small regression separates ordinary witness-assignment style data from the
stronger source-bound canonical witness-choice surface.  The cross-component
bridge annulus has honest closed-walk source data, but one of its triangular
faces contains two interior edges, so no source on this embedding can satisfy
the stronger canonical one-collar witness choice.
-/

theorem exists_two_distinct_interior_edges_on_faceBoundary_crossComponentBridgeAnnulus :
    ∃ f : AmbientFace crossComponentBridgeAnnulusEmbedding.faces,
      ∃ e₁ ∈ crossComponentBridgeAnnulusEmbedding.faceBoundary f.1,
        ∃ e₂ ∈ crossComponentBridgeAnnulusEmbedding.faceBoundary f.1,
          e₁ ≠ e₂ ∧
            e₁ ∈ interiorEdgeSupport crossComponentBridgeAnnulusEmbedding.faceBoundary
              crossComponentBridgeAnnulusEmbedding.faces ∧
              e₂ ∈ interiorEdgeSupport crossComponentBridgeAnnulusEmbedding.faceBoundary
                crossComponentBridgeAnnulusEmbedding.faces := by
  refine
    ⟨⟨(0 : CrossComponentBridgeAnnulusFace), by
        change (0 : CrossComponentBridgeAnnulusFace) ∈ crossComponentBridgeAnnulusFaces
        exact Finset.mem_univ _⟩,
      ccbR14, ?_, ccbD04, ?_, ?_, ?_, ?_⟩
  · simp [crossComponentBridgeAnnulusEmbedding, crossComponentBridgeAnnulusFaceBoundary]
  · simp [crossComponentBridgeAnnulusEmbedding, crossComponentBridgeAnnulusFaceBoundary]
  · intro h
    have hval := congrArg Subtype.val h
    simp [ccbR14, ccbD04] at hval
  · rw [crossComponentBridgeAnnulus_interiorEdgeSupport_eq]
    simp [crossComponentBridgeAnnulusInteriorEdges]
  · rw [crossComponentBridgeAnnulus_interiorEdgeSupport_eq]
    simp [crossComponentBridgeAnnulusInteriorEdges]

theorem not_nonempty_planarBoundaryCanonicalWitnessChoice_crossComponentBridgeAnnulus
    (source :
      PlanarBoundaryClosedWalkAnnulusBoundarySource crossComponentBridgeAnnulusEmbedding) :
    ¬ Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        source.toPlanarBoundaryAnnulusBoundaryData) := by
  exact
    not_nonempty_planarBoundaryCanonicalWitnessChoice_of_exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusBoundarySource
      source
      exists_two_distinct_interior_edges_on_faceBoundary_crossComponentBridgeAnnulus

theorem
    not_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_crossComponentBridgeAnnulus :
    ¬ ∃ source :
        PlanarBoundaryClosedWalkAnnulusBoundarySource crossComponentBridgeAnnulusEmbedding,
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData) := by
  rintro ⟨source, hChoice⟩
  exact not_nonempty_planarBoundaryCanonicalWitnessChoice_crossComponentBridgeAnnulus source hChoice

theorem
    closedWalkAnnulusBoundarySource_boundaryCyclePair_does_not_imply_canonicalWitnessChoice_crossComponentBridgeAnnulus :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource crossComponentBridgeAnnulusEmbedding) ∧
      AnnulusBoundaryCyclePair crossComponentBridgeAnnulusEmbedding
        crossComponentBridgeAnnulusOuterBoundarySet
        crossComponentBridgeAnnulusInnerBoundarySet ∧
        ¬ ∃ source :
            PlanarBoundaryClosedWalkAnnulusBoundarySource crossComponentBridgeAnnulusEmbedding,
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              source.toPlanarBoundaryAnnulusBoundaryData) :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_crossComponentBridgeAnnulus,
    annulusBoundaryCyclePair_crossComponentBridgeAnnulus,
    not_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_crossComponentBridgeAnnulus⟩

end Theorem49BoundaryZeroForcedEdgeRegression

end Mettapedia.GraphTheory.FourColor
