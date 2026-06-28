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

/-- The repaired two-band annulus has a concrete ambient face with two distinct interior edges.
This is the source-side canonical-witness obstruction left after the split boundary has already
been repaired by component inducedness and cross-component chord-freeness. -/
theorem exists_two_distinct_interior_edges_on_faceBoundary_twoBandAnnulus :
    ∃ f : AmbientFace twoBandAnnulusEmbedding.faces,
      ∃ e₁ ∈ twoBandAnnulusEmbedding.faceBoundary f.1,
        ∃ e₂ ∈ twoBandAnnulusEmbedding.faceBoundary f.1,
          e₁ ≠ e₂ ∧
            e₁ ∈ interiorEdgeSupport twoBandAnnulusEmbedding.faceBoundary
              twoBandAnnulusEmbedding.faces ∧
              e₂ ∈ interiorEdgeSupport twoBandAnnulusEmbedding.faceBoundary
                twoBandAnnulusEmbedding.faces := by
  refine
    ⟨⟨(0 : TwoBandAnnulusFace), by
        change (0 : TwoBandAnnulusFace) ∈ twoBandAnnulusFaces
        exact Finset.mem_univ _⟩,
      tbaR14, ?_, tbaM34, ?_, ?_, ?_, ?_⟩
  · simp [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary]
  · simp [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary]
  · intro h
    have hval := congrArg Subtype.val h
    simp [tbaR14, tbaM34] at hval
  · rw [twoBandAnnulus_interiorEdgeSupport_eq]
    simp [twoBandAnnulusInteriorEdges]
  · rw [twoBandAnnulus_interiorEdgeSupport_eq]
    simp [twoBandAnnulusInteriorEdges]

theorem not_nonempty_planarBoundaryCanonicalWitnessChoice_twoBandAnnulus
    (source :
      PlanarBoundaryClosedWalkAnnulusBoundarySource twoBandAnnulusEmbedding) :
    ¬ Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        source.toPlanarBoundaryAnnulusBoundaryData) := by
  exact
    not_nonempty_planarBoundaryCanonicalWitnessChoice_of_exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusBoundarySource
      source
      exists_two_distinct_interior_edges_on_faceBoundary_twoBandAnnulus

theorem
    not_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_twoBandAnnulus :
    ¬ ∃ source :
        PlanarBoundaryClosedWalkAnnulusBoundarySource twoBandAnnulusEmbedding,
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData) := by
  rintro ⟨source, hChoice⟩
  exact not_nonempty_planarBoundaryCanonicalWitnessChoice_twoBandAnnulus source hChoice

/-- Strong source-bound canonical-witness counterexample packet.  The two-band annulus has the
repaired closed-walk, selected-boundary, component-induced, cross-component-chord-free,
chord-free, carrier, and nonempty interior-support geometry, but no closed-walk source on this
embedding can supply the canonical facewise witness choice. -/
theorem twoBandAnnulus_repairedBoundaryGeometry_counterexample_to_canonicalWitnessChoice :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData twoBandAnnulusEmbedding) ∧
      Nonempty
          (PlanarBoundaryClosedWalkAnnulusBoundarySource twoBandAnnulusEmbedding) ∧
        AnnulusBoundaryCyclePair twoBandAnnulusEmbedding
            twoBandAnnulusOuterBoundarySet
            twoBandAnnulusInnerBoundarySet ∧
          selectedBoundarySupport
              twoBandAnnulusEmbedding.faceBoundary
              twoBandAnnulusEmbedding.faces
              twoBandAnnulusEmbedding.faces =
            twoBandAnnulusOuterBoundarySet ∪ twoBandAnnulusInnerBoundarySet ∧
            BoundaryEdgeSetInducedSubgraph twoBandAnnulusOuterBoundarySet ∧
              BoundaryEdgeSetInducedSubgraph twoBandAnnulusInnerBoundarySet ∧
                BoundaryEdgeSetCrossComponentChordFree
                  twoBandAnnulusOuterBoundarySet
                  twoBandAnnulusInnerBoundarySet ∧
                  SelectedBoundaryInducedSubgraph twoBandAnnulusEmbedding ∧
                    InteriorEdgesNotSelectedBoundaryChords twoBandAnnulusEmbedding ∧
                      (selectedBoundaryInteriorEdgeEndpointVertices
                        twoBandAnnulusEmbedding).Nonempty ∧
                        twoBandAnnulusInteriorEdges.Nonempty ∧
                          ¬ ∃ source :
                              PlanarBoundaryClosedWalkAnnulusBoundarySource
                                twoBandAnnulusEmbedding,
                            Nonempty
                              (PlanarBoundaryCanonicalWitnessChoice
                                source.toPlanarBoundaryAnnulusBoundaryData) := by
  rcases twoBandAnnulus_boundaryCyclePair_componentInduced_crossComponentChordFree_positive_packet with
    ⟨hsource, hcycles, hsupport, houterInduced, hinnerInduced, hcrossFree,
      hselectedInduced, hnoChord, hcarrier⟩
  exact
    ⟨⟨twoBandAnnulusAnnulusBoundaryReachabilityData⟩,
      hsource,
      hcycles,
      hsupport,
      houterInduced,
      hinnerInduced,
      hcrossFree,
      hselectedInduced,
      hnoChord,
      hcarrier,
      ⟨tbaR03, by simp [twoBandAnnulusInteriorEdges]⟩,
      not_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_twoBandAnnulus⟩

end Theorem49BoundaryZeroForcedEdgeRegression

end Mettapedia.GraphTheory.FourColor
