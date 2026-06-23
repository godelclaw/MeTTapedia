import Mettapedia.GraphTheory.FourColor.Theorem49ResidualBoundaryRouteCore

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open Theorem49ForcingInteriorEdgeObstruction
open Theorem49InteriorVerticesEndpointObstruction
open Theorem49PlanarBoundaryAnnulusHonestGeometryRegression

variable {V : Type*} [DecidableEq V]


/-- Exact Step 2 residual seed on one peeled face of the explicit-Tait diamond benchmark.  This
shows the repaired exact-v23 shell is genuinely inhabited on the same fixed embedding where the
honest facewise-at-most-one route already closes to full theorem-4.9 synthesis. -/
theorem nonempty_diamondWithTriangleFace0_v23ResidualBoundaryInitialState :
    Nonempty
      (V23ResidualBoundaryInitialState diamondWithTriangleTaitEdgeColoring red blue
        (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)) := by
  exact
    ⟨residualBoundaryInitialState_of_sum_v23_single_component_purifications_eq_boundaryOnlyGenerator
      diamondWithTriangleTaitEdgeColoring red blue
      (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)⟩

/-- The explicit-Tait diamond benchmark concretely inhabits the repaired exact-v23 honest-source
facewise-at-most-one branch.  On that same fixed embedding the branch reaches full
`Theorem49BoundaryRootSynthesis`, but still cannot carry either the current endpoint witness or
the projected nonempty theorem-4.9 endpoint. -/
theorem
    diamondWithTriangle_closedWalkSource_tait_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState diamondWithTriangleTaitEdgeColoring red blue
          (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
              diamondWithTriangleEmbedding.faces)).card ≤
          (1 : ℕ)) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData := by
    exact
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleClosedWalkAnnulusBoundarySource
        diamondWithTriangle_atMostOneInteriorEdgePerFace
  have hNoEndpoint :
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding := by
    exact
      not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleClosedWalkAnnulusBoundarySource
        diamondWithTriangle_atMostOneInteriorEdgePerFace
  have hNoProjected :
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring := by
    exact
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleClosedWalkAnnulusBoundarySource
        diamondWithTriangle_atMostOneInteriorEdgePerFace
        diamondWithTriangleTaitEdgeColoring
  exact
    ⟨⟨diamondWithTriangleClosedWalkAnnulusBoundarySource⟩,
      hcurrent,
      diamondWithTriangleTaitEdgeColoring_isTait,
      nonempty_diamondWithTriangleFace0_v23ResidualBoundaryInitialState,
      diamondWithTriangle_atMostOneInteriorEdgePerFace,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring_via_atMostOneInteriorEdgePerFace,
      hNoEndpoint,
      hNoProjected⟩

/-- The same exact-v23 calibration also lives on the explicit boundary-order successor-cycle shell
of the diamond benchmark.  So the split between algebraic sufficiency and endpoint vacuity is not
peculiar to the honest closed-walk presentation. -/
theorem
    diamondWithTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryDartSuccessorCycleEmbeddingData diamondWithTriangleEmbedding) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        (diamondWithTriangleDartSuccessorCycleGeometry.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState diamondWithTriangleTaitEdgeColoring red blue
          (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
              diamondWithTriangleEmbedding.faces)).card ≤
          (1 : ℕ)) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    exact
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleClosedWalkAnnulusBoundarySource
        diamondWithTriangle_atMostOneInteriorEdgePerFace
  have hNoEndpoint :
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding := by
    exact
      not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleAnnulusBoundaryReachabilityData
        diamondWithTriangleDartSuccessorCycleGeometry
        diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        diamondWithTriangle_atMostOneInteriorEdgePerFace
  have hNoProjected :
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring := by
    exact
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleAnnulusBoundaryReachabilityData
        diamondWithTriangleDartSuccessorCycleGeometry
        diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        diamondWithTriangle_atMostOneInteriorEdgePerFace
        diamondWithTriangleTaitEdgeColoring
  exact
    ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
      ⟨diamondWithTriangleDartSuccessorCycleGeometry⟩,
      diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      diamondWithTriangleTaitEdgeColoring_isTait,
      nonempty_diamondWithTriangleFace0_v23ResidualBoundaryInitialState,
      diamondWithTriangle_atMostOneInteriorEdgePerFace,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring_via_atMostOneInteriorEdgePerFace,
      hNoEndpoint,
      hNoProjected⟩

/-- The repaired exact-v23 honest-source facewise-at-most-one diamond shell is not blocked at
witness ownership either.  On the same fixed embedding, the canonical one-collar annulus witness
assignment is already nonempty before the branch runs into the live endpoint impossibility. -/
theorem
    diamondWithTriangle_closedWalkSource_tait_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState diamondWithTriangleTaitEdgeColoring red blue
          (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
              diamondWithTriangleEmbedding.faces)).card ≤
          (1 : ℕ)) ∧
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData)) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring := by
  rcases
    diamondWithTriangle_closedWalkSource_tait_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
      with
    ⟨hSource, hcurrent, hTait, hv23, hAtMostOne, hSynth, hNoEndpoint, hNoProjected⟩
  have hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData)) := by
    rcases
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace with
      ⟨choice⟩
    exact ⟨choice.toPlanarBoundaryAnnulusWitnessAssignment⟩
  exact
    ⟨hSource, hcurrent, hTait, hv23, hAtMostOne, hwitness, hSynth, hNoEndpoint, hNoProjected⟩

/-- The same exact-v23 witness-ownership upgrade also lives on the explicit successor-cycle shell
of the diamond benchmark.  So on this repaired at-most-one branch, the route is not blocked at
same-embedding annulus witness assignment either. -/
theorem
    diamondWithTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryDartSuccessorCycleEmbeddingData diamondWithTriangleEmbedding) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        (diamondWithTriangleDartSuccessorCycleGeometry.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState diamondWithTriangleTaitEdgeColoring red blue
          (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
              diamondWithTriangleEmbedding.faces)).card ≤
          (1 : ℕ)) ∧
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData)) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring := by
  rcases
    diamondWithTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
      with
    ⟨hBoundaryData, hDarts, hArc, hcurrent, hTait, hv23, hAtMostOne, hSynth, hNoEndpoint,
      hNoProjected⟩
  have hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData)) := by
    rcases
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace with
      ⟨choice⟩
    exact ⟨choice.toPlanarBoundaryAnnulusWitnessAssignment⟩
  exact
    ⟨hBoundaryData, hDarts, hArc, hcurrent, hTait, hv23, hAtMostOne, hwitness, hSynth,
      hNoEndpoint, hNoProjected⟩

/-- The explicit-Tait diamond benchmark shows that the repaired exact-v23 honest-source
facewise-at-most-one branch remains strictly weaker than the heavier annulus-root peel packages.
On the same fixed embedding it reaches full `Theorem49BoundaryRootSynthesis`, but still fails the
interior-dual adj-distance, annulus-root adj-distance, and annulus-root parent-peel targets. -/
theorem diamondWithTriangle_closedWalkSource_exactV23_facewiseAtMostOne_consolidatedRouteDiagnosis
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState diamondWithTriangleTaitEdgeColoring red blue
          (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
              diamondWithTriangleEmbedding.faces)).card ≤
          (1 : ℕ)) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
  rcases
    diamondWithTriangle_closedWalkSource_tait_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
      with
  ⟨hSource, hcurrent, hTait, hv23, hAtMostOne, hSynth, hNoEndpoint, hNoProjected⟩
  have hNoInteriorDual :
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
    simpa using
      (diamondWithTriangle_explicitTait_synthesis_without_interiorDualBoundaryRootAdjDistancePeelData).2.2
  have hNoAdjDistance :
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData diamondWithTriangleEmbedding) := by
    simpa using
      (diamondWithTriangle_explicitTait_synthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData).2.2
  have hNoParentPeel :
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
    simpa using
      (diamondWithTriangle_explicitTait_synthesis_without_planarBoundaryAnnulusRootParentPeelData).2.2
  exact
    ⟨hSource, hcurrent, hTait, hv23, hAtMostOne, hSynth, hNoEndpoint, hNoProjected,
      hNoInteriorDual, hNoAdjDistance, hNoParentPeel⟩

/-- The same strengthened diagnosis also holds on the explicit successor-cycle presentation of the
diamond benchmark.  So these heavier annulus-root peel targets are not rescued by passing from
the honest closed-walk source to the boundary-order route shell. -/
theorem diamondWithTriangle_successorCycle_exactV23_facewiseAtMostOne_consolidatedRouteDiagnosis
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryDartSuccessorCycleEmbeddingData diamondWithTriangleEmbedding) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        (diamondWithTriangleDartSuccessorCycleGeometry.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState diamondWithTriangleTaitEdgeColoring red blue
          (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
              diamondWithTriangleEmbedding.faces)).card ≤
          (1 : ℕ)) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
  rcases
    diamondWithTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
      with
  ⟨hBoundaryData, hDarts, hArc, hcurrent, hTait, hv23, hAtMostOne, hSynth, hNoEndpoint,
    hNoProjected⟩
  have hNoInteriorDual :
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
    simpa using
      (diamondWithTriangle_explicitTait_synthesis_without_interiorDualBoundaryRootAdjDistancePeelData).2.2
  have hNoAdjDistance :
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData diamondWithTriangleEmbedding) := by
    simpa using
      (diamondWithTriangle_explicitTait_synthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData).2.2
  have hNoParentPeel :
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
    simpa using
      (diamondWithTriangle_explicitTait_synthesis_without_planarBoundaryAnnulusRootParentPeelData).2.2
  exact
    ⟨hBoundaryData, hDarts, hArc, hcurrent, hTait, hv23, hAtMostOne, hSynth, hNoEndpoint,
      hNoProjected, hNoInteriorDual, hNoAdjDistance, hNoParentPeel⟩

/-- Closed-walk exact-shell parent-peel route: the same repaired exact-v23/v23.5 shell also
reaches the raw quotient/error endpoint for every Kirchhoff chain on the resulting purified
carrier. -/
theorem
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        source _hcurrent C₀ _hv23 parentData _hparentBoundary hEndpoint)
      C₀ hC₀ hx

/-- Successor-cycle form of the same exact-shell parent-peel raw quotient/error closure. -/
theorem
    theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
      (theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles _hselectedBoundaryArc _hcurrent C₀ _hv23 parentData
        _hparentBoundary hEndpoint)
      C₀ hC₀ hx

/-- Closed-walk exact-shell adj-distance route: once the repaired one-collar v23/v23.5 shell
already carries generic boundary-root adjacency-distance data and an unblocked endpoint, the
projected theorem-4.9 endpoint is immediate. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            source.boundaryFaceRoots hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        source _hcurrent C₀ _hv23 peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hchildren hEndpoint)
      C₀ hC₀

/-- Successor-cycle form of the same exact-shell rooted-cover projected endpoint closure. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc _hcurrent C₀ _hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint)
      C₀ hC₀

/-- Closed-walk exact-shell adj-distance route: once the repaired one-collar v23/v23.5 shell
already carries generic boundary-root adjacency-distance data and an unblocked endpoint, the
projected theorem-4.9 endpoint is immediate. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        source _hcurrent C₀ _hv23 interiorData hEndpoint)
      C₀ hC₀

/-- Successor-cycle form of the same exact-shell adj-distance projected endpoint closure. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles _hselectedBoundaryArc _hcurrent C₀ _hv23 interiorData
        hEndpoint)
      C₀ hC₀

/-- Closed-walk exact-shell adj-distance route: the same repaired one-collar shell also reaches
the raw quotient/error endpoint for every Kirchhoff chain on the resulting purified carrier. -/
theorem
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            source.boundaryFaceRoots hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        source _hcurrent C₀ _hv23 peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hchildren hEndpoint)
      C₀ hC₀ hx

/-- Successor-cycle form of the same exact-shell rooted-cover raw quotient/error closure. -/
theorem
    theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc _hcurrent C₀ _hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint)
      C₀ hC₀ hx

/-- Closed-walk exact-shell adj-distance route: the same repaired one-collar shell also reaches
the raw quotient/error endpoint for every Kirchhoff chain on the resulting purified carrier. -/
theorem
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        source _hcurrent C₀ _hv23 interiorData hEndpoint)
      C₀ hC₀ hx

/-- Successor-cycle form of the same exact-shell adj-distance raw quotient/error closure. -/
theorem
    theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles _hselectedBoundaryArc _hcurrent C₀ _hv23 interiorData
        hEndpoint)
      C₀ hC₀ hx

/-- Existential closed-walk exact-shell rooted-cover data reaches the graph-level projected
theorem-4.9 endpoint for any supplied Tait coloring. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              source.boundaryFaceRoots hcoverRoots hsepRoots)
            source.fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb)
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases h with
    ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, peelFaces, hunique, hcoverRoots,
      hsepRoots, hpeelInterior, hcover, hchildren, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hC₀ hv23 peelFaces hunique hcoverRoots hsepRoots hpeelInterior
        hcover hchildren hEndpoint⟩

/-- Successor-cycle exact-shell rooted-cover data reaches the graph-level projected theorem-4.9
endpoint for any supplied Tait coloring. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb)
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren,
      hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint⟩

/-- Existential closed-walk exact-shell rooted-cover data and a Kirchhoff chain on the same
embedding reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              source.boundaryFaceRoots hcoverRoots hsepRoots)
            source.fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb ∧
        x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases h with
    ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, peelFaces, hunique, hcoverRoots,
      hsepRoots, hpeelInterior, hcover, hchildren, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hC₀ hv23 peelFaces hunique hcoverRoots hsepRoots hpeelInterior
        hcover hchildren hEndpoint hx⟩

/-- Successor-cycle exact-shell rooted-cover data and a Kirchhoff chain on the same embedding
reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb ∧
        x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren,
      hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint hx⟩

/-- Existential closed-walk exact-shell parent-peel data reaches the graph-level projected
theorem-4.9 endpoint for any supplied Tait coloring. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData ∧
          HasUnblockedInteriorEndpoint emb)
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases h with
    ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, parentData, hparentBoundary, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hC₀ hv23 parentData hparentBoundary hEndpoint⟩

/-- Successor-cycle exact-shell parent-peel data reaches the graph-level projected theorem-4.9
endpoint for any supplied Tait coloring. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          HasUnblockedInteriorEndpoint emb)
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      parentData, hparentBoundary, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 parentData
        hparentBoundary hEndpoint⟩

/-- Existential closed-walk exact-shell parent-peel data and a Kirchhoff chain on the same
embedding reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData ∧
          HasUnblockedInteriorEndpoint emb ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases h with
    ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, parentData, hparentBoundary, hEndpoint,
      hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hC₀ hv23 parentData hparentBoundary hEndpoint hx⟩

/-- Successor-cycle exact-shell parent-peel data and a Kirchhoff chain on the same embedding
reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          HasUnblockedInteriorEndpoint emb ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      parentData, hparentBoundary, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 parentData
        hparentBoundary hEndpoint hx⟩

/-- Existential closed-walk exact-shell adj-distance data reaches the graph-level projected
theorem-4.9 endpoint for any supplied Tait coloring. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb)
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases h with ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, interiorData, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hC₀ hv23 interiorData hEndpoint⟩

/-- Successor-cycle exact-shell adj-distance data reaches the graph-level projected theorem-4.9
endpoint for any supplied Tait coloring. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb)
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      interiorData, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 interiorData
        hEndpoint⟩

/-- Existential closed-walk exact-shell adj-distance data and a Kirchhoff chain on the same
embedding reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases h with
    ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, interiorData, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hC₀ hv23 interiorData hEndpoint hx⟩

/-- Successor-cycle exact-shell adj-distance data and a Kirchhoff chain on the same embedding
reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      interiorData, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 interiorData
        hEndpoint hx⟩

theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData
        source data C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData
        boundaryData dartCycles hselectedBoundaryArc data C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
          HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
              HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc data hEndpoint C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
          HasUnblockedInteriorEndpoint emb ∧
            x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C₀ hC₀ hx⟩

theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
              HasUnblockedInteriorEndpoint emb ∧
                x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc data hEndpoint C₀ hC₀ hx⟩

theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ResidualBoundarySelectorData emb))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData
        source data C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (ResidualBoundarySelectorData emb))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData
        boundaryData dartCycles hselectedBoundaryArc data C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ResidualBoundarySelectorData emb) ∧
          HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (ResidualBoundarySelectorData emb) ∧
              HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc data hEndpoint C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ResidualBoundarySelectorData emb) ∧
          HasUnblockedInteriorEndpoint emb ∧
            x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C₀ hC₀ hx⟩

theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (ResidualBoundarySelectorData emb) ∧
              HasUnblockedInteriorEndpoint emb ∧
                x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc data hEndpoint C₀ hC₀ hx⟩

theorem
    exists_embedding_residualBoundaryPositiveProjectedGeometryOn_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
          HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint⟩

theorem
    exists_embedding_residualBoundaryPositiveProjectedGeometryOn_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
              HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc data hEndpoint⟩

theorem
    exists_embedding_currentBoundaryRemainders_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
          HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint⟩
  rcases
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      source data hEndpoint with
    ⟨i, f, hf, hremainders⟩
  exact ⟨emb, data, i, f, hf, hremainders⟩

theorem
    exists_embedding_currentBoundaryRemainders_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
              HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint⟩
  rcases
    theorem49CurrentBoundaryRemainders_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      boundaryData dartCycles hselectedBoundaryArc data hEndpoint with
    ⟨i, f, hf, hremainders⟩
  exact ⟨emb, data, i, f, hf, hremainders⟩

theorem
    exists_embedding_residualBoundaryPositiveProjectedGeometryOn_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ResidualBoundarySelectorData emb) ∧
          HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint⟩

theorem
    exists_embedding_residualBoundaryPositiveProjectedGeometryOn_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (ResidualBoundarySelectorData emb) ∧
              HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc data hEndpoint⟩

theorem
    exists_embedding_currentBoundaryRemainders_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ResidualBoundarySelectorData emb) ∧
          HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint⟩
  rcases
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      source data hEndpoint with
    ⟨i, f, hf, hremainders⟩
  exact
    ⟨emb, data.toResidualBoundaryLayerFacePeelWitnessData, i, f, hf, hremainders⟩

theorem
    exists_embedding_currentBoundaryRemainders_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (ResidualBoundarySelectorData emb) ∧
              HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint⟩
  rcases
    theorem49CurrentBoundaryRemainders_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      boundaryData dartCycles hselectedBoundaryArc data hEndpoint with
    ⟨i, f, hf, hremainders⟩
  exact
    ⟨emb, data.toResidualBoundaryLayerFacePeelWitnessData, i, f, hf, hremainders⟩

namespace Theorem49ResidualBoundaryRoute

open Theorem49PositiveGeometricSourceConstruction

theorem counterEmbedding_residualBoundaryPositiveProjectedGeometryOn :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn
      Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      Theorem49PlanarBoundaryAnnulusGeometryRegression.counterCollarGeometry
      counterEmbedding_hasUnblockedInteriorEndpoint

theorem counterEmbedding_boundaryRootNonemptyProjectedSynthesis_via_residualBoundary
    [Fintype Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph.edgeSet]
    [FiniteDimensional F2
      (Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph.edgeSet → Color)] :
    Theorem49BoundaryRootNonemptyProjectedSynthesis
      Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding
      counterGraphTaitEdgeColoring := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      Theorem49PlanarBoundaryAnnulusGeometryRegression.counterCollarGeometry
      counterEmbedding_hasUnblockedInteriorEndpoint
      counterGraphTaitEdgeColoring counterGraphTaitEdgeColoring_isTait

/-- Stronger calibration of the two-collar positive benchmark: the residual/current-boundary
positive shell already reaches the nonempty projected theorem-4.9 endpoint on the same
embedding, while a forcing interior edge still blocks both the selector and construction
face-layer shells there. -/
theorem
    counterEmbedding_residualBoundaryPositiveProjectedGeometryOn_and_boundaryRootNonemptyProjectedSynthesis_and_forcingInteriorEdgeWitness_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData
    [Fintype Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph.edgeSet]
    [FiniteDimensional F2
      (Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph.edgeSet → Color)] :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn
        Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding ∧
      Theorem49BoundaryRootNonemptyProjectedSynthesis
        Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding
        counterGraphTaitEdgeColoring ∧
      Nonempty
        (ForcingInteriorEdgeWitness
          Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding) ∧
      ¬ Nonempty
        (BoundaryFreeIncidentFaceSelector
          Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionFaceLayerData
          Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding) := by
  exact
    ⟨counterEmbedding_residualBoundaryPositiveProjectedGeometryOn,
      counterEmbedding_boundaryRootNonemptyProjectedSynthesis_via_residualBoundary,
      nonempty_forcingInteriorEdgeWitness_counterEmbedding,
      not_nonempty_boundaryFreeIncidentFaceSelector_counterEmbedding,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData
        (emb := Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding)
        counterEmbeddingForcingInteriorEdgeWitness⟩

/-- The two-collar positive benchmark already inhabits the residual/current-boundary positive
shell while still failing both the boundary-free selector shell and the downstream construction
face-layer shell on the same embedding.  So the residual wrapper itself does not repair that
selector/construction gap. -/
theorem
    counterEmbedding_residualBoundaryPositiveProjectedGeometryOn_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData
    :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn
        Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding ∧
      ¬ Nonempty
        (BoundaryFreeIncidentFaceSelector
          Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionFaceLayerData
          Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding) := by
  exact
    ⟨counterEmbedding_residualBoundaryPositiveProjectedGeometryOn,
      not_nonempty_boundaryFreeIncidentFaceSelector_counterEmbedding,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData
        (emb := Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding)
        counterEmbeddingForcingInteriorEdgeWitness⟩

/-- Residual/current-boundary positive geometry does not universally produce a boundary-free
incident-face selector on the same embedding.  The two-collar positive benchmark already carries
the residual shell while its forcing edge blocks every selector. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_theorem49ResidualBoundaryPositiveProjectedGeometryOn_counterGraph
    :
    ¬ ∀ {emb :
          PlaneEmbeddingWithBoundary
            Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph},
        Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb →
          Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  exact
    not_nonempty_boundaryFreeIncidentFaceSelector_counterEmbedding
      (h (emb := Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding)
        counterEmbedding_residualBoundaryPositiveProjectedGeometryOn)

/-- The same residual/current-boundary positive shell also does not universally produce the
downstream construction face-layer package on the same embedding.  So even after passing through
the residual wrapper, the selector/construction burden remains genuinely open. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_theorem49ResidualBoundaryPositiveProjectedGeometryOn_counterGraph
    :
    ¬ ∀ {emb :
          PlaneEmbeddingWithBoundary
            Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph},
        Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb →
          Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData
        (emb := Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding)
        counterEmbeddingForcingInteriorEdgeWitness
      (h (emb := Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding)
        counterEmbedding_residualBoundaryPositiveProjectedGeometryOn)

/-- Graph-level classification of the same two-collar benchmark: for the explicit constant Tait
coloring, the residual/current-boundary positive shell and the projected theorem-4.9 endpoint
already coexist on one embedding with a forcing interior edge and failure of both the selector
and construction face-layer shells. -/
theorem
    counterGraph_explicitTait_residualBoundaryPositiveProjectedGeometry_and_boundaryRootNonemptyProjectedSynthesis_with_forcingInteriorEdgeWitness_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData
    [Fintype Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph.edgeSet]
    [FiniteDimensional F2
      (Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph.edgeSet → Color)] :
    IsTaitEdgeColoring
        Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph
        counterGraphTaitEdgeColoring ∧
      (∃ emb :
          PlaneEmbeddingWithBoundary
            Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph,
        Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∧
          Theorem49BoundaryRootNonemptyProjectedSynthesis
            emb counterGraphTaitEdgeColoring ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
          ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb)) := by
  exact
    ⟨counterGraphTaitEdgeColoring_isTait,
      ⟨Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding,
        counterEmbedding_residualBoundaryPositiveProjectedGeometryOn_and_boundaryRootNonemptyProjectedSynthesis_and_forcingInteriorEdgeWitness_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData⟩⟩

end Theorem49ResidualBoundaryRoute

end Mettapedia.GraphTheory.FourColor
