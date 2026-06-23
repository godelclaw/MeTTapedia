import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestGeometryRegressionBenchmarks
import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstruction

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49PlanarBoundaryAnnulusHonestGeometryRegression

open Theorem49InteriorVerticesEndpointObstruction

/-- Local forcing-edge witness reused to compare the honest diamond benchmark against the current
parent-peel route. -/
def diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry :
    Theorem49ForcingInteriorEdgeObstruction.ForcingInteriorEdgeWitness diamondWithTriangleEmbedding
    where
  edge := dt12
  heInterior := dt12_mem_interiorEdgeSupport
  hforcing := by
    intro f hf
    exact exists_selectedBoundarySupport_of_dt12_mem_faceBoundary_diamondWithTriangle hf

/-- The diamond-with-triangle model is the positive benchmark for the current same-embedding
geometry ladder under an actual Tait coloring: the honest closed-walk source, canonical witness
choice, collar geometry, certificate-level witnesses, and theorem-4.9 boundary-root synthesis all
coexist on the same embedding. -/
theorem
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice,
      diamondWithTriangleTaitEdgeColoring_isTait,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasCollarLayerFacePeelWitnessData,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring⟩

/-- Parallel sealing of the diamond benchmark: on the same genuine cyclic source embedding, the
full current same-embedding positive geometry stack and theorem-4.9 synthesis endpoint coexist
with complete failure of the newer projected nonempty endpoint, because selected-boundary
purification deletes both endpoints of the unique interior edge. -/
theorem
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_nonemptyProjectedSynthesis
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice,
      diamondWithTriangleTaitEdgeColoring_isTait,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasCollarLayerFacePeelWitnessData,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      by
        intro hProjected
        exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle
          hProjected.nonemptySynthesis.carrier_nonempty⟩

/-- Graph-level packaging of the same diamond obstruction: the graph admits an honest
closed-walk source together with the full current same-embedding geometry stack and theorem-4.9
synthesis for an explicit Tait coloring, yet the projected nonempty endpoint still fails on that
same embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) ∧
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  rcases
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_nonemptyProjectedSynthesis
      with ⟨hSource, hChoice, hTait, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth, _,
        hNoProjected⟩
  rcases hSource with ⟨_source⟩
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      hChoice,
      diamondWithTriangleTaitEdgeColoring,
      hTait,
      hCollar,
      hPrev,
      hLayer,
      hHeight,
      hCert,
      hWell,
      hSynth,
      hNoProjected⟩

/-- The diamond benchmark refutes the live converse from the full current same-embedding
geometry stack back to the projected nonempty theorem-4.9 endpoint.  Even an honest closed-walk
annulus source with canonical witness choice, explicit Tait coloring, annulus collar geometry,
repaired previous-boundary witness geometry, all currently sufficient peel witnesses, and the
full theorem-4.9 synthesis package does not force `Theorem49BoundaryRootNonemptyProjectedSynthesis`
on the same embedding. -/
theorem
    not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              source.toPlanarBoundaryAnnulusBoundaryData) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
                Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
                Nonempty
                  (BoundaryRootedFacePeelCertificate emb.faces.attach
                    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
                Theorem49BoundaryRootSynthesis emb C →
                Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb source =>
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
              Theorem49BoundaryRootSynthesis emb C →
              Theorem49BoundaryRootNonemptyProjectedSynthesis emb C) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph
      with ⟨emb, source, hChoice, C, hC, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth,
        hNoProjected⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoProjected (hTarget hChoice C hC hCollar hPrev hLayer hHeight hCert hWell hSynth)⟩

/-- Parallel sealing of the diamond benchmark against the current interior-dual route: on the
same genuine cyclic source embedding, the full current same-embedding positive geometry stack and
the explicit-Tait theorem-4.9 synthesis endpoint already hold, yet generic
`InteriorDualBoundaryRootAdjDistancePeelData` still fails. -/
theorem
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_interiorDualBoundaryRootAdjDistancePeelData
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice,
      diamondWithTriangleTaitEdgeColoring_isTait,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasCollarLayerFacePeelWitnessData,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle⟩

/-- Graph-level packaging of the same diamond obstruction against the earlier generic
interior-dual route: the graph admits an honest closed-walk source together with the full
current same-embedding geometry stack and theorem-4.9 synthesis for an explicit Tait coloring,
yet generic `InteriorDualBoundaryRootAdjDistancePeelData` still fails on that same embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) ∧
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Nonempty
                (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  rcases
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_interiorDualBoundaryRootAdjDistancePeelData
      with ⟨hSource, hChoice, hTait, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth,
        hNoIDBRAD⟩
  rcases hSource with ⟨_source⟩
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      hChoice,
      diamondWithTriangleTaitEdgeColoring,
      hTait,
      hCollar,
      hPrev,
      hLayer,
      hHeight,
      hCert,
      hWell,
      hSynth,
      hNoIDBRAD⟩

/-- The diamond benchmark also refutes the converse from the full current same-embedding
geometry stack and theorem-4.9 synthesis back to the earlier generic
`InteriorDualBoundaryRootAdjDistancePeelData` package. -/
theorem
    not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              source.toPlanarBoundaryAnnulusBoundaryData) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
                Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
                Nonempty
                  (BoundaryRootedFacePeelCertificate emb.faces.attach
                    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty
                  (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb source =>
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
              Theorem49BoundaryRootSynthesis emb C →
              Nonempty
                (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangleGraph
      with ⟨emb, source, hChoice, C, hC, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth,
        hNoIDBRAD⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoIDBRAD (hTarget hChoice C hC hCollar hPrev hLayer hHeight hCert hWell hSynth)⟩

/-- The same genuine cyclic diamond benchmark also defeats the source-preserving annulus-root
adjacency-distance target itself: even the full current same-embedding positive geometry stack
and the explicit-Tait theorem-4.9 synthesis endpoint do not force
`PlanarBoundaryAnnulusRootAdjDistancePeelData` on that embedding. -/
theorem
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_planarBoundaryAnnulusRootAdjDistancePeelData
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData diamondWithTriangleEmbedding) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice,
      diamondWithTriangleTaitEdgeColoring_isTait,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasCollarLayerFacePeelWitnessData,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      Theorem49ForcingInteriorEdgeObstruction.not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry⟩

/-- Parallel sealing of the diamond benchmark against the live parent-peel target: on the same
genuine cyclic source embedding, the full current same-embedding positive geometry stack and the
explicit-Tait theorem-4.9 synthesis endpoint already hold, yet the stronger
`PlanarBoundaryAnnulusRootParentPeelData` package still fails. -/
theorem
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_planarBoundaryAnnulusRootParentPeelData
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice,
      diamondWithTriangleTaitEdgeColoring_isTait,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasCollarLayerFacePeelWitnessData,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      Theorem49ForcingInteriorEdgeObstruction.not_nonempty_planarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry⟩

/-- Graph-level packaging of the same diamond obstruction: the graph admits an honest
closed-walk source together with the full current same-embedding geometry stack and theorem-4.9
synthesis for an explicit Tait coloring, yet the source-preserving annulus-root adj-distance
package still fails on that same embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) ∧
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  rcases
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_planarBoundaryAnnulusRootAdjDistancePeelData
      with ⟨hSource, hChoice, hTait, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth,
        hNoAdj⟩
  rcases hSource with ⟨_source⟩
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      hChoice,
      diamondWithTriangleTaitEdgeColoring,
      hTait,
      hCollar,
      hPrev,
      hLayer,
      hHeight,
      hCert,
      hWell,
      hSynth,
      hNoAdj⟩

/-- The diamond benchmark refutes the converse from the full current same-embedding geometry
stack and theorem-4.9 synthesis back to the source-preserving annulus-root adjacency-distance
package.  Even an honest closed-walk annulus source with canonical witness choice, explicit
Tait coloring, annulus collar geometry, repaired previous-boundary witness geometry, all
currently sufficient peel witnesses, and the full theorem-4.9 synthesis package does not force
`PlanarBoundaryAnnulusRootAdjDistancePeelData` on the same embedding. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              source.toPlanarBoundaryAnnulusBoundaryData) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
                Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
                Nonempty
                  (BoundaryRootedFacePeelCertificate emb.faces.attach
                    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb source =>
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
              Theorem49BoundaryRootSynthesis emb C →
              Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb)) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph
      with ⟨emb, source, hChoice, C, hC, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth,
        hNoAdj⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoAdj (hTarget hChoice C hC hCollar hPrev hLayer hHeight hCert hWell hSynth)⟩

/-- Graph-level packaging of the same diamond obstruction against the live parent-peel target:
the graph admits an honest closed-walk source together with the full current same-embedding
geometry stack and theorem-4.9 synthesis for an explicit Tait coloring, yet the stronger
annulus-root parent-peel package still fails on that same embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) ∧
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  rcases
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_planarBoundaryAnnulusRootParentPeelData
      with ⟨hSource, hChoice, hTait, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth,
        hNoParent⟩
  rcases hSource with ⟨_source⟩
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      hChoice,
      diamondWithTriangleTaitEdgeColoring,
      hTait,
      hCollar,
      hPrev,
      hLayer,
      hHeight,
      hCert,
      hWell,
      hSynth,
      hNoParent⟩

/-- The diamond benchmark also refutes the converse from the full current same-embedding
geometry stack and theorem-4.9 synthesis back to the live annulus-root parent-peel target. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              source.toPlanarBoundaryAnnulusBoundaryData) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
                Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
                Nonempty
                  (BoundaryRootedFacePeelCertificate emb.faces.attach
                    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb source =>
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
              Theorem49BoundaryRootSynthesis emb C →
              Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb)) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph
      with ⟨emb, source, hChoice, C, hC, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth,
        hNoParent⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact
        hNoParent (hTarget hChoice C hC hCollar hPrev hLayer hHeight hCert hWell hSynth)⟩

/-- Consolidated route diagnosis for the genuine cyclic diamond benchmark: the same explicit
Tait-colored embedding already carries the full current same-embedding positive geometry stack and
the theorem-4.9 synthesis endpoint, while its raw interior-edge endpoint carrier is still
nonempty, its selected-boundary-purified carrier is empty, the projected nonempty endpoint fails,
generic interior-dual boundary-root adjacency-distance data fails, and the live parent-peel
package fails as well. -/
theorem diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_consolidatedRouteDiagnosis
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      (interiorEdgeEndpointSupport diamondWithTriangleEmbedding).Nonempty ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
  rcases
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_nonemptyProjectedSynthesis
      with ⟨hSource, hChoice, hTait, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynthesis,
        hPurifiedEmpty, hNotProjected⟩
  rcases
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_interiorDualBoundaryRootAdjDistancePeelData
      with ⟨_, _, _, _, _, _, _, _, _, _, hNoIDBRAD⟩
  rcases
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_planarBoundaryAnnulusRootParentPeelData
      with ⟨_, _, _, _, _, _, _, _, _, _, hNoParentPeel⟩
  exact
    ⟨hSource,
      hChoice,
      hTait,
      hCollar,
      hPrev,
      hLayer,
      hHeight,
      hCert,
      hWell,
      hSynthesis,
      interiorEdgeEndpointSupport_nonempty_diamondWithTriangle,
      hPurifiedEmpty,
      hNotProjected,
      hNoIDBRAD,
      hNoParentPeel⟩

/-- The same explicit Tait-colored positive benchmark already reaches the full theorem-4.9
synthesis endpoint while still failing the generic interior-dual boundary-root adj-distance
package.  So the current generic adj-distance burden is not necessary even on a genuine cyclic
synthesis model. -/
theorem diamondWithTriangle_explicitTait_synthesis_without_interiorDualBoundaryRootAdjDistancePeelData
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    ⟨diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle⟩

/-- The same explicit Tait-colored positive benchmark already reaches the full theorem-4.9
synthesis endpoint while still failing the source-preserving annulus-root adj-distance target. -/
theorem diamondWithTriangle_explicitTait_synthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData diamondWithTriangleEmbedding) := by
  exact
    ⟨diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      Theorem49ForcingInteriorEdgeObstruction.not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry⟩

/-- The same explicit Tait-colored positive benchmark already reaches the full theorem-4.9
synthesis endpoint while still failing the live parent-oriented annulus-root target.  So the
current parent-peel burden is not necessary even on a genuine cyclic synthesis model. -/
theorem diamondWithTriangle_explicitTait_synthesis_without_planarBoundaryAnnulusRootParentPeelData
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
  exact
    ⟨diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      Theorem49ForcingInteriorEdgeObstruction.not_nonempty_planarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry⟩

/-- The same explicit Tait-colored positive benchmark does not reach the nonempty-carrier
version of the theorem-4.9 synthesis target: the selected-boundary purification deletes both
endpoints of its sole interior edge. -/
theorem not_theorem49BoundaryRootNonemptySynthesis_diamondWithTriangle_explicitTait
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ Theorem49BoundaryRootNonemptySynthesis diamondWithTriangleEmbedding
      diamondWithTriangleTaitEdgeColoring := by
  intro h
  exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle
    h.carrier_nonempty

/-- No coloring can put the diamond-with-triangle embedding into the current projected nonempty
theorem-4.9 endpoint: that package contains the nonempty-carrier synthesis package, while the
selected-boundary purification has already deleted both endpoints of the only interior edge. -/
theorem not_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangle
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)]
    (C0 : diamondWithTriangleGraph.EdgeColoring Color) :
    ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding C0 := by
  intro h
  exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle
    h.nonemptySynthesis.carrier_nonempty

/-- Compact status theorem for the explicit Tait-colored diamond benchmark: current synthesis is
available on the same embedding, but the nonempty selected-boundary interior-edge endpoint target
is not. -/
theorem diamondWithTriangle_explicitTait_synthesis_has_empty_selectedBoundaryInteriorCarrier
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ Theorem49BoundaryRootNonemptySynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring := by
  exact
    ⟨diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      not_theorem49BoundaryRootNonemptySynthesis_diamondWithTriangle_explicitTait⟩

/-- The explicit Tait-colored diamond benchmark reaches the current synthesis target through the
same-embedding geometry stack, but the newer projected nonempty endpoint is blocked outright by
the empty purified endpoint carrier. -/
theorem diamondWithTriangle_explicitTait_synthesis_blocks_nonemptyProjectedSynthesis
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring := by
  exact
    ⟨diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangle
        diamondWithTriangleTaitEdgeColoring⟩

/-- The at-most-one route reaches the same explicit-Tait diamond endpoint, but it still does not
solve the nonempty-carrier obligation: selected-boundary purification deletes both endpoints of
the sole interior edge. -/
theorem diamondWithTriangle_explicitTait_atMostOne_synthesis_has_empty_selectedBoundaryInteriorCarrier
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ Theorem49BoundaryRootNonemptySynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring := by
  exact
    ⟨diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring_via_atMostOneInteriorEdgePerFace,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      not_theorem49BoundaryRootNonemptySynthesis_diamondWithTriangle_explicitTait⟩

/-- Honest annulus source data on the diamond-with-triangle embedding is compatible with the
weak one-collar annulus geometry and its attached certificate, but still incompatible with the
construction-side parent-witness orientation shell.  This shows the certificate lane sits strictly
earlier than the parent-orientation lane even on a genuine cyclic source model. -/
theorem
    closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_without_parentWitnessOrientation_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      ¬ diamondWithTriangleOneCollarConstruction.ParentWitnessOrientation := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      not_diamondWithTriangleOneCollarConstructionParentWitnessOrientation⟩

/-- The same honest-source one-collar annulus geometry already reaches the attached-certificate
endpoint on the diamond-with-triangle embedding, while the interior-dual boundary-root
adjacency-distance package remains empty there.  This is a genuine source-side witness that the
certificate branch is available strictly earlier than the current interior-dual route. -/
theorem
    closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_without_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle⟩

/-- The same honest-source one-collar annulus geometry and attached certificate still do not
force the live parent-oriented annulus-root target on the diamond-with-triangle embedding.  So
the certificate lane is already strictly earlier than the current parent-peel burden on a genuine
cyclic source model. -/
theorem
    closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_without_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      Theorem49ForcingInteriorEdgeObstruction.not_nonempty_planarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry⟩

/-- Graph-level packaging of the honest diamond collar/certificate obstruction against the
generic interior-dual route: the graph admits an honest closed-walk annulus source together with
weak one-collar geometry, an attached rooted face-peel certificate, and an explicit Tait coloring
reaching theorem-4.9 synthesis, yet generic boundary-root adjacency-distance data still fails on
that same embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Nonempty
                (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleTaitEdgeColoring,
      diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle⟩

/-- The honest diamond collar/certificate benchmark refutes the converse from weak one-collar
geometry, an attached rooted face-peel certificate, and explicit theorem-4.9 synthesis back to
the generic boundary-root adjacency-distance package. -/
theorem
    not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
            Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty
                  (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Theorem49BoundaryRootSynthesis emb C →
              Nonempty
                (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangleGraph
      with ⟨emb, source, hCollar, hCert, C, hC, hSynth, hNoIDBRAD⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoIDBRAD (hTarget hCollar hCert C hC hSynth)⟩

/-- Graph-level packaging of the same honest diamond collar/certificate obstruction against the
source-preserving annulus-root adjacency-distance route target. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleTaitEdgeColoring,
      diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      Theorem49ForcingInteriorEdgeObstruction.not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry⟩

/-- The honest diamond collar/certificate benchmark also refutes the converse from that same
certificate-plus-synthesis shell back to the source-preserving annulus-root adj-distance target. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
            Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Theorem49BoundaryRootSynthesis emb C →
              Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb)) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph
      with ⟨emb, source, hCollar, hCert, C, hC, hSynth, hNoAdj⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoAdj (hTarget hCollar hCert C hC hSynth)⟩

/-- Graph-level packaging of the same honest diamond collar/certificate obstruction against the
live source-fixed annulus-root parent-peel target. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleTaitEdgeColoring,
      diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      Theorem49ForcingInteriorEdgeObstruction.not_nonempty_planarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry⟩

/-- The honest diamond collar/certificate benchmark refutes the converse from weak annulus
geometry, attached certificate, and explicit theorem-4.9 synthesis back to the live parent-peel
route target. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
            Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Theorem49BoundaryRootSynthesis emb C →
              Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb)) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph
      with ⟨emb, source, hCollar, hCert, C, hC, hSynth, hNoParent⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoParent (hTarget hCollar hCert C hC hSynth)⟩

/-- The weak honest collar/certificate shell already reaches explicit theorem-4.9 synthesis on
the diamond benchmark, but the selected-boundary-purified carrier is still empty, so the
projected nonempty endpoint fails there as well. -/
theorem
    diamondWithTriangle_explicitTait_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_theorem49BoundaryRootSynthesis_blocks_nonemptyProjectedSynthesis
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangle
        diamondWithTriangleTaitEdgeColoring⟩

/-- Graph-level packaging of the same honest diamond collar/certificate obstruction against the
projected nonempty theorem-4.9 endpoint itself. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleTaitEdgeColoring,
      diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangle
        diamondWithTriangleTaitEdgeColoring⟩

/-- The honest diamond collar/certificate benchmark also refutes the converse from that weak
certificate-plus-synthesis shell to the projected nonempty theorem-4.9 endpoint. -/
theorem
    not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
            Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Theorem49BoundaryRootSynthesis emb C →
                Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Theorem49BoundaryRootSynthesis emb C →
              Theorem49BoundaryRootNonemptyProjectedSynthesis emb C) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph
      with ⟨emb, source, hCollar, hCert, C, hC, hSynth, hNoProjected⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoProjected (hTarget hCollar hCert C hC hSynth)⟩

/-- Genuine honest-source annulus geometry and the attached certificate endpoint still do not
force the endpoint-support separation needed by the current non-vacuous annulus-root repair.
The diamond-with-triangle embedding already has an honest closed-walk source, a one-collar
annulus geometry, an attached rooted face-peel certificate, and a nonempty raw interior-edge
endpoint carrier, yet the shared diamond endpoint still lies on the selected boundary support. -/
theorem
    closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_with_nonempty_interiorEdgeEndpointSupport_without_endpointSupport_disjoint_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      (interiorEdgeEndpointSupport diamondWithTriangleEmbedding).Nonempty ∧
      ¬ Disjoint (interiorEdgeEndpointSupport diamondWithTriangleEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces)) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      interiorEdgeEndpointSupport_nonempty_diamondWithTriangle,
      not_endpointSupport_disjoint_diamondWithTriangle⟩

/-- The same honest source model already satisfies the repaired previous-boundary witness
geometry and therefore reaches the boundary-aware well-founded peel endpoint, but the raw
interior-edge endpoint carrier still meets the selected boundary support. So endpoint-support
disjointness is not forced even by the corrected annulus geometry surface that feeds the
well-founded certificate route. -/
theorem
    closedWalkAnnulusBoundarySource_and_previousBoundaryWitnessGeometry_and_wellFoundedFacePeelWitnessData_with_nonempty_interiorEdgeEndpointSupport_without_endpointSupport_disjoint_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      (interiorEdgeEndpointSupport diamondWithTriangleEmbedding).Nonempty ∧
      ¬ Disjoint (interiorEdgeEndpointSupport diamondWithTriangleEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces)) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      interiorEdgeEndpointSupport_nonempty_diamondWithTriangle,
      not_endpointSupport_disjoint_diamondWithTriangle⟩

/-- The stronger honest-source countermodel reaches the repaired previous-boundary witness
geometry and the derived boundary-aware well-founded peel endpoint, and still has a nonempty raw
interior-edge endpoint carrier while the purified selected-boundary carrier is empty.  This
directly blocks non-vacuous endpoint purification on the current honest annulus route. -/
theorem
    closedWalkAnnulusBoundarySource_and_previousBoundaryWitnessGeometry_and_wellFoundedFacePeelWitnessData_with_nonempty_interiorEdgeEndpointSupport_and_empty_selectedBoundaryInteriorEdgeEndpointVertices_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      (interiorEdgeEndpointSupport diamondWithTriangleEmbedding).Nonempty ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ (selectedBoundaryInteriorEdgeEndpointVertices
        diamondWithTriangleEmbedding).Nonempty := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      interiorEdgeEndpointSupport_nonempty_diamondWithTriangle,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle⟩

/-- The same honest-source countermodel already reaches the explicit height-ordered peel witness
surface obtained from the corrected previous-boundary annulus geometry, and still has nonempty raw
interior-edge endpoint support while the purified selected-boundary carrier is empty. So even this
stronger layered peel interface does not force the non-vacuous endpoint carrier needed by the
current theorem-4.9 repair line. -/
theorem
    closedWalkAnnulusBoundarySource_and_previousBoundaryWitnessGeometry_and_heightOrderedFacePeelWitnessData_with_nonempty_interiorEdgeEndpointSupport_and_empty_selectedBoundaryInteriorEdgeEndpointVertices_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      (interiorEdgeEndpointSupport diamondWithTriangleEmbedding).Nonempty ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ (selectedBoundaryInteriorEdgeEndpointVertices
        diamondWithTriangleEmbedding).Nonempty := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData,
      interiorEdgeEndpointSupport_nonempty_diamondWithTriangle,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle⟩

/-- A general sufficient condition for canonical witness choice on an honest source.

If every face has at most one interior boundary edge, every face has a fallback boundary edge, and
every non-interior boundary edge already lies on the source's outer or inner ambient boundary,
then the canonical facewise witness choice exists.  The witness is the unique interior edge on a
face when one exists, and the fallback edge otherwise. -/
theorem exists_canonicalWitnessChoice_of_closedWalkSource_with_atMostOneInteriorEdgePerFace
    [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hfallback : ∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
          (1 : ℕ))
    (h_nonInterior_on_ambient :
      ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
        e ∈ emb.faceBoundary f.1 →
          e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
          e ∈
            source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
              source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    Nonempty
      (PlanarBoundaryCanonicalWitnessChoice source.toPlanarBoundaryAnnulusBoundaryData) := by
  exact
    exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
      source fallbackEdge hfallback h_at_most_one_interior h_nonInterior_on_ambient

/-- Graph-level version of the at-most-one-interior-edge sufficient condition. -/
theorem admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_closedWalkSource_with_atMostOneInteriorEdgePerFace
    [DecidableEq V]
    {G : SimpleGraph V}
    (hex :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                  ((emb.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                    (1 : ℕ)) ∧
                  ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                    e ∈ emb.faceBoundary f.1 →
                      e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                      e ∈
                        source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                          source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    AdmitsPlanarBoundaryAnnulusWitnessAssignment G := by
  classical
  obtain ⟨emb, source, fallbackEdge, hfb, hatmost, hnonInterior⟩ := hex
  exact
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_planarBoundaryCanonicalWitnessChoice
      ⟨emb, source.toPlanarBoundaryAnnulusBoundaryData,
        exists_canonicalWitnessChoice_of_closedWalkSource_with_atMostOneInteriorEdgePerFace source
          fallbackEdge hfb hatmost hnonInterior⟩

/-- Closed-walk annulus source together with at-most-one-interior-edge-per-face directly
implies weak collar geometry. This chains witness-assignment derivation from the at-most-one
interior condition with the existing witness-to-geometry bridge. -/
theorem admitsPlanarBoundaryAnnulusCollarGeometry_of_exists_closedWalkSource_with_atMostOneInteriorEdgePerFace
    [DecidableEq V]
    {G : SimpleGraph V}
    (hex :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                  ((emb.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                    (1 : ℕ)) ∧
                  ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                    e ∈ emb.faceBoundary f.1 →
                      e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                      e ∈
                        source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                          source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    AdmitsPlanarBoundaryAnnulusCollarGeometry G :=
  admitsPlanarBoundaryAnnulusCollarGeometry_of_admitsPlanarBoundaryAnnulusWitnessAssignment
    (admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_closedWalkSource_with_atMostOneInteriorEdgePerFace
      hex)

/-- The chained-diamonds canonical witness selector is a valid fallback boundary edge on every
ambient face.  This is the facewise fallback component needed to instantiate the generic
at-most-one-interior-edge criterion. -/
theorem chainedDiamondsCanonicalWitnessEdge_mem :
    ∀ f : AmbientFace chainedDiamondsWithTriangleEmbedding.faces,
      chainedDiamondsCanonicalWitnessEdge f ∈
        chainedDiamondsWithTriangleEmbedding.faceBoundary f.1 := by
  intro f
  obtain ⟨⟨i, hi⟩, hf⟩ := f
  interval_cases i <;>
    simp [chainedDiamondsCanonicalWitnessEdge, chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsWithTriangleFaceBoundary, cdt01, cdt12, cdt02, cdt13, cdt23,
      cdt34, cdt45, cdt35, cdt46, cdt56, cdt78, cdt89, cdt97]

/-- On the chained-diamonds honest source, every face-boundary edge that is not one of the two
interior edges already lies on the extracted outer or inner ambient annulus boundary. -/
theorem chainedDiamonds_nonInteriorOnAmbient :
    ∀ (f : AmbientFace chainedDiamondsWithTriangleEmbedding.faces)
        {e : chainedDiamondsWithTriangleGraph.edgeSet},
      e ∈ chainedDiamondsWithTriangleEmbedding.faceBoundary f.1 →
        e ∉ interiorEdgeSupport chainedDiamondsWithTriangleEmbedding.faceBoundary
          chainedDiamondsWithTriangleEmbedding.faces →
        e ∈
          chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
            chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary := by
  intro _f e _he hnonInterior
  have heSelected :
      e ∈ selectedBoundarySupport chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
    rcases chainedDiamondsWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cdt01_mem_selectedBoundarySupport
    · exact False.elim (hnonInterior cdt12_mem_interiorEdgeSupport)
    · exact cdt02_mem_selectedBoundarySupport
    · exact cdt13_mem_selectedBoundarySupport
    · exact cdt23_mem_selectedBoundarySupport
    · exact cdt34_mem_selectedBoundarySupport
    · exact False.elim (hnonInterior cdt45_mem_interiorEdgeSupport)
    · exact cdt35_mem_selectedBoundarySupport
    · exact cdt46_mem_selectedBoundarySupport
    · exact cdt56_mem_selectedBoundarySupport
    · exact cdt78_mem_selectedBoundarySupport
    · exact cdt89_mem_selectedBoundarySupport
    · exact cdt97_mem_selectedBoundarySupport
  exact
    chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData
      |>.hambientBoundaryCover heSelected

/-- Concrete non-vacuity of the at-most-one-interior-edge sufficient condition: the
chained-diamonds honest closed-walk source supplies all local hypotheses of the generic
criterion. -/
theorem
    exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces →
            chainedDiamondsWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : chainedDiamondsWithTriangleGraph.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary := by
  exact
    ⟨chainedDiamondsWithTriangleEmbedding, chainedDiamondsClosedWalkAnnulusBoundarySource,
      chainedDiamondsCanonicalWitnessEdge, chainedDiamondsCanonicalWitnessEdge_mem,
      chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace,
      chainedDiamonds_nonInteriorOnAmbient⟩

/-- Status theorem for the chained-diamonds at-most-one benchmark: it inhabits the local
at-most-one source package, but it cannot supply either a surviving purified carrier or a Tait
coloring. -/
theorem chainedDiamonds_atMostOne_source_has_empty_carrier_and_no_tait :
    (∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → chainedDiamondsWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : chainedDiamondsWithTriangleGraph.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) ∧
      selectedBoundaryInteriorEdgeEndpointVertices chainedDiamondsWithTriangleEmbedding = ∅ ∧
      ¬ (selectedBoundaryInteriorEdgeEndpointVertices
          chainedDiamondsWithTriangleEmbedding).Nonempty ∧
      ¬ ∃ C : chainedDiamondsWithTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C := by
  exact
    ⟨exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_chainedDiamondsWithTriangle,
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_chainedDiamondsWithTriangle,
      not_exists_taitEdgeColoring_chainedDiamondsWithTriangleGraph⟩

/-- The generic at-most-one-interior-edge criterion reconstructs the chained-diamonds canonical
witness choice; this proves the criterion is inhabited by a model with two distinct interior
edges. -/
theorem
    chainedDiamondsClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace :
    Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) := by
  exact
    exists_canonicalWitnessChoice_of_closedWalkSource_with_atMostOneInteriorEdgePerFace
      chainedDiamondsClosedWalkAnnulusBoundarySource
      chainedDiamondsCanonicalWitnessEdge
      chainedDiamondsCanonicalWitnessEdge_mem
      chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace
      chainedDiamonds_nonInteriorOnAmbient

/-- Graph-level witness-assignment admissibility for chained diamonds obtained through the
generic at-most-one-interior-edge theorem, not through the hand-built canonical witness object. -/
theorem
    chainedDiamondsWithTriangleGraph_admitsPlanarBoundaryAnnulusWitnessAssignment_via_atMostOneInteriorEdgePerFace :
    AdmitsPlanarBoundaryAnnulusWitnessAssignment chainedDiamondsWithTriangleGraph := by
  exact
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_closedWalkSource_with_atMostOneInteriorEdgePerFace
      exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph

/-- Graph-level collar-geometry admissibility for chained diamonds obtained through the generic
at-most-one-interior-edge sufficient condition. -/
theorem
    chainedDiamondsWithTriangleGraph_admitsPlanarBoundaryAnnulusCollarGeometry_via_atMostOneInteriorEdgePerFace :
    AdmitsPlanarBoundaryAnnulusCollarGeometry chainedDiamondsWithTriangleGraph := by
  exact
    admitsPlanarBoundaryAnnulusCollarGeometry_of_exists_closedWalkSource_with_atMostOneInteriorEdgePerFace
      exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph

/-- Conditional theorem-4.9 synthesis for chained diamonds obtained through the generic
at-most-one-interior-edge sufficient condition, rather than through the hand-built one-collar
geometry.  The statement remains conditional on a Tait coloring, as this benchmark is primarily
a non-vacuity test for the local annulus geometry criterion. -/
theorem
    chainedDiamondsWithTriangleEmbedding_theorem49BoundaryRootSynthesis_via_atMostOneInteriorEdgePerFace
    [Fintype chainedDiamondsWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (chainedDiamondsWithTriangleGraph.edgeSet → Color)]
    (C₀ : chainedDiamondsWithTriangleGraph.EdgeColoring Color)
    (hC₀ : IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C₀) :
    Theorem49BoundaryRootSynthesis chainedDiamondsWithTriangleEmbedding C₀ := by
  rcases
    chainedDiamondsClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace
      with ⟨choice⟩
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
      (G := chainedDiamondsWithTriangleGraph)
      choice.toPlanarBoundaryAnnulusWitnessAssignment C₀ hC₀

/-- Graph-level theorem-4.9 synthesis for chained diamonds through the generic at-most-one
sufficient condition. -/
theorem
    exists_theorem49BoundaryRootSynthesis_chainedDiamondsWithTriangleGraph_via_atMostOneInteriorEdgePerFace
    [Fintype chainedDiamondsWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (chainedDiamondsWithTriangleGraph.edgeSet → Color)]
    (C₀ : chainedDiamondsWithTriangleGraph.EdgeColoring Color)
    (hC₀ : IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
      exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph
      C₀ hC₀

/-- The chained-diamonds at-most-one benchmark already inhabits the exact one-collar current-
boundary shell and the split-annulus witness-assignment surface on the same honest closed-walk
source, but the purified carrier stays empty and no Tait coloring exists.  So on this branch the
remaining obstruction is not current-boundary or witness-assignment packaging. -/
theorem
    exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_chainedDiamondsWithTriangleGraph_with_empty_carrier_and_without_taitEdgeColoring :
    ∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ)) ∧
        Nonempty
          (PlanarBoundaryAnnulusWitnessAssignment
            (planarBoundaryAnnulusDecomposition_of_boundaryData
              source.toPlanarBoundaryAnnulusBoundaryData)) ∧
        selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ ∧
        ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
        ¬ ∃ C : chainedDiamondsWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData chainedDiamondsWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData := by
    exact
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        chainedDiamondsClosedWalkAnnulusBoundarySource
        chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace
  have hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData)) := by
    rcases
      chainedDiamondsClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace
        with ⟨choice⟩
    exact ⟨choice.toPlanarBoundaryAnnulusWitnessAssignment⟩
  exact
    ⟨chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsClosedWalkAnnulusBoundarySource,
      hcurrent,
      chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace,
      hwitness,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_chainedDiamondsWithTriangle,
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_chainedDiamondsWithTriangle,
      not_exists_taitEdgeColoring_chainedDiamondsWithTriangleGraph⟩

/-- The same chained-diamonds benchmark already reaches the exact one-collar current-boundary
shell and split-annulus witness assignment on a fixed honest source, and any hypothetical Tait
coloring would already close to full theorem-4.9 synthesis on that same embedding.  The actual
remaining blocker on this branch is therefore the absence of any Tait coloring, not missing
current-boundary or witness-assignment packaging. -/
theorem
    exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_theorem49BoundaryRootSynthesis_for_any_taitEdgeColoring_chainedDiamondsWithTriangleGraph_without_any_taitEdgeColoring
    [Fintype chainedDiamondsWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (chainedDiamondsWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ)) ∧
        Nonempty
          (PlanarBoundaryAnnulusWitnessAssignment
            (planarBoundaryAnnulusDecomposition_of_boundaryData
              source.toPlanarBoundaryAnnulusBoundaryData)) ∧
        (∀ C : chainedDiamondsWithTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C →
            Theorem49BoundaryRootSynthesis emb C) ∧
        selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ ∧
        ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
        ¬ ∃ C : chainedDiamondsWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData chainedDiamondsWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData := by
    exact
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        chainedDiamondsClosedWalkAnnulusBoundarySource
        chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace
  have hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData)) := by
    rcases
      chainedDiamondsClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace
        with ⟨choice⟩
    exact ⟨choice.toPlanarBoundaryAnnulusWitnessAssignment⟩
  exact
    ⟨chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsClosedWalkAnnulusBoundarySource,
      hcurrent,
      chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace,
      hwitness,
      (fun C hC =>
        chainedDiamondsWithTriangleEmbedding_theorem49BoundaryRootSynthesis_via_atMostOneInteriorEdgePerFace
          C hC),
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_chainedDiamondsWithTriangle,
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_chainedDiamondsWithTriangle,
      not_exists_taitEdgeColoring_chainedDiamondsWithTriangleGraph⟩

end Theorem49PlanarBoundaryAnnulusHonestGeometryRegression

end Mettapedia.GraphTheory.FourColor
