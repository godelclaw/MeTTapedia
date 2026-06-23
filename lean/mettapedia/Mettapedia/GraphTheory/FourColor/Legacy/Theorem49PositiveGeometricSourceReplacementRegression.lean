import Mettapedia.GraphTheory.FourColor.Theorem49SharedInteriorPairReplacementBenchmark

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression

namespace Theorem49PositiveGeometricSourceReplacementRegression

/-- Honest closed-walk source data, a Tait coloring, and an explicit unblocked interior endpoint
do not universally force any current direct or route-facing replacement positive package. -/
theorem not_forall_any_replacementPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
          HasUnblockedInteriorEndpoint emb →
          Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
            Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
              Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair
  rcases hAny with hHeight | hRest
  · exact not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair hHeight
  · rcases hRest with hCollar | hRest
    · exact not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair hCollar
    · rcases hRest with hClosedWalk | hSuccessorCycle
      · exact
          not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
            hClosedWalk
      · exact
          not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
            hSuccessorCycle

/-- Exact one-collar current-boundary data still does not upgrade the honest closed-walk source,
Tait coloring, and endpoint witness into any current replacement positive package. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            HasUnblockedInteriorEndpoint emb →
            Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
              Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                  Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding sharedInteriorPairClosedWalkAnnulusBoundarySource
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource)
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair
  rcases hAny with hHeight | hRest
  · exact not_theorem49HeightOrderedPositiveProjectedGeometryOn_sharedInteriorPair hHeight
  · rcases hRest with hCollar | hRest
    · exact not_theorem49CollarLayerPositiveProjectedGeometryOn_sharedInteriorPair hCollar
    · rcases hRest with hClosedWalk | hSuccessorCycle
      · exact
          not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
            hClosedWalk
      · exact
          not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_sharedInteriorPair
            hSuccessorCycle

/-- Honest closed-walk source data, a Tait coloring, and an explicit unblocked interior endpoint
do not universally force even the raw height-ordered or collar-layer witness-cover data. -/
theorem not_forall_some_witnessCoverData_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
          HasUnblockedInteriorEndpoint emb →
          Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
            Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair
  rcases hAny with hHeight | hCollar
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar

/-- Honest closed-walk source data, a Tait coloring, and an explicit unblocked interior endpoint
do not universally force any of the current sufficient same-embedding geometric endpoints. -/
theorem not_forall_some_currentSufficientSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
          HasUnblockedInteriorEndpoint emb →
          Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
            Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
            Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∨
            Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
            Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      hasUnblockedInteriorEndpoint_sharedInteriorPair
  rcases hAny with hHeight | hCollar | hAttached | hWellFounded | hAnnulus
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar
  · exact not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair hAttached
  · exact not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair hWellFounded
  · exact not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair hAnnulus

/-- The named endpoint witness still does not upgrade the exact one-collar current-boundary
honest-source shell into any current sufficient same-embedding geometric endpoint. -/
theorem
    not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            HasUnblockedInteriorEndpoint emb →
            Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∨
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  exact
    not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_sharedInteriorPair
      (by
        intro emb source hcurrent hcolor hnonempty
        exact
          h emb source hcurrent hcolor
            ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
              emb).2 hnonempty))

end Theorem49PositiveGeometricSourceReplacementRegression

end Mettapedia.GraphTheory.FourColor
