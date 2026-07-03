import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryZeroForcedEdgeRegression
import Mettapedia.GraphTheory.FourColor.Theorem49CollarLayerPositiveGeometry

/-!
Route-facing positive-geometry refutations for the two-band boundary-zero regression shell.

The large boundary-zero regression file proves the concrete repaired two-band shell and the raw
absence of height-ordered witness-cover data.  This module packages that obstruction at the
positive-geometry API consumed by the replacement route.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace Theorem49BoundaryZeroForcedEdgePositiveGeometryRegression

open Theorem49BoundaryZeroForcedEdgeRegression

/-- The two-band annulus has no boundary-aware well-founded parent witness-cover data on the
same embedding.  Such data canonically lowers to height-ordered witness-cover data, already
refuted by the cardinality obstruction in the boundary-zero regression file. -/
theorem not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_twoBandAnnulus :
    ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData twoBandAnnulusEmbedding) := by
  rintro ⟨data⟩
  exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_twoBandAnnulus
    ⟨data.toPlanarBoundaryHeightOrderedFacePeelWitnessData⟩

/-- The two-band annulus has no height-ordered replacement-positive geometry on the same
embedding. -/
theorem not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoBandAnnulus :
    ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn twoBandAnnulusEmbedding := by
  exact
    not_heightOrderedPositiveProjectedGeometryOn_of_not_nonempty_heightOrderedFacePeelWitnessData
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_twoBandAnnulus

/-- The equivalent finite collar-layer replacement-positive geometry is impossible on the same
two-band embedding as well. -/
theorem not_theorem49CollarLayerPositiveProjectedGeometryOn_twoBandAnnulus :
    ¬ Theorem49CollarLayerPositiveProjectedGeometryOn twoBandAnnulusEmbedding := by
  intro hCollar
  exact not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoBandAnnulus
    (heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn.2
      hCollar)

/-- Route-facing repaired-geometry counterexample packet: the two-band annulus has the repaired
closed-walk and selected-boundary geometry used by the surviving finite route packets, but it
still carries no well-founded parent witness-cover data and neither current direct
replacement-positive geometry surface. -/
theorem
    twoBandAnnulus_repairedBoundaryGeometry_counterexample_to_replacementPositiveGeometry :
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
                          ¬ Nonempty
                            (PlanarBoundaryWellFoundedFacePeelWitnessData
                              twoBandAnnulusEmbedding) ∧
                            ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
                              twoBandAnnulusEmbedding ∧
                              ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
                                twoBandAnnulusEmbedding := by
  rcases
    twoBandAnnulus_repairedBoundaryGeometry_counterexample_to_heightOrderedFacePeelWitnessData
    with
    ⟨hReach, hSource, hCycles, hSupport, hOuterInduced, hInnerInduced, hCrossFree,
      hSelectedInduced, hNoChord, hCarrier, hInterior, _hNoHeight⟩
  exact
    ⟨hReach,
      hSource,
      hCycles,
      hSupport,
      hOuterInduced,
      hInnerInduced,
      hCrossFree,
      hSelectedInduced,
      hNoChord,
      hCarrier,
      hInterior,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_twoBandAnnulus,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoBandAnnulus,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_twoBandAnnulus⟩

/-- Strong route-facing repaired-geometry counterexample packet.  The same two-band annulus has
the repaired closed-walk, selected-boundary, chord-free, carrier, and nonempty interior-support
geometry, but it simultaneously refutes both current replacement-positive geometry surfaces and
the outside-crossing side-cut repair. -/
theorem
    twoBandAnnulus_repairedBoundaryGeometry_counterexample_to_positiveGeometry_and_sideCut :
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
                          ¬ Nonempty
                            (PlanarBoundaryWellFoundedFacePeelWitnessData
                              twoBandAnnulusEmbedding) ∧
                            ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
                              twoBandAnnulusEmbedding ∧
                              ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
                                twoBandAnnulusEmbedding ∧
                                (¬ ∃ side : Fin 9 → Prop,
                                  ∀ e : twoBandAnnulusGraph.edgeSet,
                                    e ∈ interiorEdgeSupport
                                        twoBandAnnulusEmbedding.faceBoundary
                                        twoBandAnnulusEmbedding.faces →
                                      EdgeCrossesVertexSide twoBandAnnulusGraph side e) ∧
                                  ¬ ∃ side : Fin 9 → Prop,
                                    ∀ e : twoBandAnnulusGraph.edgeSet,
                                      e ∈ twoBandAnnulusInteriorEdges →
                                        EdgeCrossesVertexSide
                                          twoBandAnnulusGraph side e := by
  rcases
    twoBandAnnulus_repairedBoundaryGeometry_counterexample_to_replacementPositiveGeometry
    with
    ⟨hReach, hSource, hCycles, hSupport, hOuterInduced, hInnerInduced, hCrossFree,
      hSelectedInduced, hNoChord, hCarrier, hInterior, hNoWellFounded, hNoHeight,
      hNoCollar⟩
  rcases
    twoBandAnnulus_repairedBoundaryGeometry_counterexample_to_sideCut_packets
    with
    ⟨_hReachSide, _hSourceSide, _hCyclesSide, _hSupportSide, _hOuterInducedSide,
      _hInnerInducedSide, _hCrossFreeSide, _hSelectedInducedSide, _hNoChordSide,
      _hCarrierSide, _hInteriorSide, hNoSupportSideCut, hNoInteriorSideCut⟩
  exact
    ⟨hReach,
      hSource,
      hCycles,
      hSupport,
      hOuterInduced,
      hInnerInduced,
      hCrossFree,
      hSelectedInduced,
      hNoChord,
      hCarrier,
      hInterior,
      hNoWellFounded,
      hNoHeight,
      hNoCollar,
      hNoSupportSideCut,
      hNoInteriorSideCut⟩

end Theorem49BoundaryZeroForcedEdgePositiveGeometryRegression

end Mettapedia.GraphTheory.FourColor
