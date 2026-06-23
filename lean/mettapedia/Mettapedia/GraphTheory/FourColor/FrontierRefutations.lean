import Mettapedia.GraphTheory.FourColor.ShellsCore
import Mettapedia.GraphTheory.FourColor.Theorem49WheelWithInnerTriangleBenchmark
import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstructionBenchmarks
import Mettapedia.GraphTheory.FourColor.Theorem49SharedInteriorPairReplacementBenchmark

/-!
# Refuted frontier oracles for Theorem 4.9

This module keeps the benchmark-heavy negative shell results separate from the
positive frontier sufficiency wrappers.  The statements show that the exact
shell hypotheses alone do not force the current geometric witness packages.
-/

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusWheelWitnessRegression
open Theorem49ForcingInteriorEdgeObstructionRegression
open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression
open Theorem49PositiveGeometricSourceReplacementRegression

/-! ## Negative lane: maximal shells that do not force the geometry -/

/-- The wheel-with-inner-triangle inhabits the full closed-walk exact shell
while refuting generic interior-dual distance-peel data.  This is the maximal
closed-walk obstruction: the shell sits strictly below the geometric layer. -/
theorem exists_closedWalkExactShell_without_interiorDualPeelData_wheel :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      Nonempty (ClosedWalkExactShell emb) ∧
        ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
          emb.faces emb.faceBoundary) := by
  obtain ⟨data, hnum, hboundary⟩ :=
    exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
  refine ⟨wheelWithInnerTriangleEmbedding, ⟨?_⟩,
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩
  exact
    { source := wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
      oneCollar := ⟨data, hnum, hboundary⟩
      tait :=
        TaitV23Data.ofTait wheelWithInnerTriangleTaitEdgeColoring
          wheelWithInnerTriangleTaitEdgeColoring_isTait red blue
          (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
      endpoint := hasUnblockedInteriorEndpoint_wheelWithInnerTriangle }

/-- Bundled form of the failed universal converse on the closed-walk branch:
no derivation can pass from the exact shell to generic interior-dual
distance-peel data. -/
theorem not_forall_interiorDualPeelData_of_closedWalkExactShell_wheel :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Nonempty (ClosedWalkExactShell emb) →
          Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
            emb.faces emb.faceBoundary) :=
  not_forall_target_of_exists_shell_witness
    exists_closedWalkExactShell_without_interiorDualPeelData_wheel

/-- The same maximal obstruction on the successor-cycle boundary-order
presentation. -/
theorem exists_successorCycleExactShell_without_interiorDualPeelData_wheel :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      Nonempty (SuccessorCycleExactShell emb) ∧
        ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
          emb.faces emb.faceBoundary) := by
  obtain ⟨data, hnum, hboundary⟩ :=
    exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace)
  refine ⟨wheelWithInnerTriangleEmbedding, ⟨?_⟩,
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩
  exact
    { boundaryReachability := wheelWithInnerTriangleAnnulusBoundaryReachabilityData
      dartCycles := wheelWithInnerTriangleDartSuccessorCycleGeometry
      selectedBoundaryArc :=
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      oneCollar := ⟨data, hnum, hboundary⟩
      tait :=
        TaitV23Data.ofTait wheelWithInnerTriangleTaitEdgeColoring
          wheelWithInnerTriangleTaitEdgeColoring_isTait red blue
          (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
      endpoint := hasUnblockedInteriorEndpoint_wheelWithInnerTriangle }

/-- Bundled failed universal converse on the successor-cycle branch. -/
theorem not_forall_interiorDualPeelData_of_successorCycleExactShell_wheel :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Nonempty (SuccessorCycleExactShell emb) →
          Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
            emb.faces emb.faceBoundary) :=
  not_forall_target_of_exists_shell_witness
    exists_successorCycleExactShell_without_interiorDualPeelData_wheel

/-- The shared-interior-pair benchmark inhabits the closed-walk exact shell
while refuting all four replacement-positive geometry packages at once.  So
the shell also sits strictly below every current sufficient same-embedding
geometry surface. -/
theorem exists_closedWalkExactShell_without_replacementPositiveGeometry_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      Nonempty (ClosedWalkExactShell emb) ∧
        ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
        ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
        ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
        ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  obtain ⟨emb, source, ⟨data, hnum, hboundary⟩, ⟨C, hC⟩, hEndpoint, h₁, h₂, h₃, h₄⟩ :=
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair
  exact
    ⟨emb,
      ⟨{ source := source
         oneCollar := ⟨data, hnum, hboundary⟩
         tait := TaitV23Data.ofTait C hC red blue ∅
         endpoint := hEndpoint }⟩,
      h₁, h₂, h₃, h₄⟩

end Mettapedia.GraphTheory.FourColor
