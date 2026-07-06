import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeMappedCutObstruction
import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeCandidateCounterexample

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Realized-candidate interface for mapped-cut face-route obstructions.

The remaining planar-normal-form proof should turn any mapped-cut face-route
obstruction into a realized finite separator candidate in the induced peeled
collar.  This module names that target and proves the reusable composition:
the obstruction-to-candidate target, together with the realized-candidate lift,
rules out mapped-cut face-route obstructions and therefore supplies the
existing mapped-cut route index.
-/

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Source-level target: every mapped-cut face-route obstruction emits a realized
finite separator candidate in the induced peeled-collar graph.
-/
def OffCarrierAttachmentMappedCutAvoidingFaceRouteObstructionRealizedCandidateTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    Prop :=
  source.OffCarrierAttachmentMappedCutAvoidingFaceRouteObstruction →
    ∃ candidate :
      CyclicSeparatorCandidate
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph,
      candidate.Realizes

/--
Under the CAP5-free regime, an obstruction-produced realized candidate is
impossible once realized candidates lift to ambient small cuts.
-/
theorem noMappedCutFaceRouteObstruction_of_obstructionRealizedCandidateTarget_of_realizedCandidateLift
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (hobstructionCandidate :
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteObstructionRealizedCandidateTarget)
    (hlift :
      PeeledCollarRealizedCandidateLiftsToAmbientSmallCut G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph) :
    ¬ source.OffCarrierAttachmentMappedCutAvoidingFaceRouteObstruction := by
  intro hobs
  rcases hobstructionCandidate hobs with ⟨candidate, hrealizes⟩
  exact
    (candidate.not_realizes_of_minimalCounterexampleRegime_of_realizedCandidateLift
      regime hlift) hrealizes

end PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Closed-walk foundation target for the planar step that remains: mapped-cut
face-route obstructions must emit realized separator candidates.
-/
def CAP5FreeClosedWalkPeeledCollarMappedCutFaceRouteObstructionRealizedCandidateFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteObstructionRealizedCandidateTarget

/--
The obstruction-to-realized-candidate foundation, plus realized-candidate
lifting, supplies the no-obstruction foundation.
-/
theorem
    cap5FreeClosedWalkNoMappedCutFaceRouteObstructionFoundationTarget_of_obstructionRealizedCandidateFoundationTarget_of_realizedCandidateLift
    (hobstructionCandidate :
      CAP5FreeClosedWalkPeeledCollarMappedCutFaceRouteObstructionRealizedCandidateFoundationTarget)
    (hlift :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarNoMappedCutFaceRouteObstructionFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.noMappedCutFaceRouteObstruction_of_obstructionRealizedCandidateTarget_of_realizedCandidateLift
      regime (hobstructionCandidate source regime) (hlift regime)

/--
The same inputs supply the mapped-cut avoiding face-route foundation consumed
by the existing route index.
-/
theorem
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_obstructionRealizedCandidateFoundationTarget_of_realizedCandidateLift
    (hobstructionCandidate :
      CAP5FreeClosedWalkPeeledCollarMappedCutFaceRouteObstructionRealizedCandidateFoundationTarget)
    (hlift :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget :=
  cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_noMappedCutFaceRouteObstructionFoundationTarget
    (cap5FreeClosedWalkNoMappedCutFaceRouteObstructionFoundationTarget_of_obstructionRealizedCandidateFoundationTarget_of_realizedCandidateLift
      hobstructionCandidate hlift)

/--
Public foundation index for the obstruction-to-realized-candidate route.  The
first two fields are the existing annulus separation targets; the last two
fields are the closed-walk obstruction-to-candidate target and the graph-facing
realized-candidate lift target.
-/
def CAP5FreePeeledCollarMappedCutObstructionRealizedCandidateFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarMappedCutFaceRouteObstructionRealizedCandidateFoundationTarget ∧
    CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget

/--
The obstruction-to-realized-candidate index supplies the mapped-cut foundation
index, so downstream uses do not carry cyclic five-edge-connectivity as a
hypothesis.
-/
theorem
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_obstructionRealizedCandidateFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarMappedCutObstructionRealizedCandidateFoundationTargetIndex) :
    CAP5FreePeeledCollarMappedCutFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_obstructionRealizedCandidateFoundationTarget_of_realizedCandidateLift
      hindex.2.2.1 hindex.2.2.2⟩

/--
Closed-walk route-index theorem for the obstruction-to-realized-candidate
foundation package.
-/
theorem
    section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget_of_obstructionRealizedCandidateFoundationTargets
    (hobstructionCandidate :
      CAP5FreeClosedWalkPeeledCollarMappedCutFaceRouteObstructionRealizedCandidateFoundationTarget)
    (hlift :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget :=
  section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget
    (cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_obstructionRealizedCandidateFoundationTarget_of_realizedCandidateLift
      hobstructionCandidate hlift)

/--
The obstruction-to-realized-candidate public index supplies the mapped-cut
route indices, plus the graph-facing realized-candidate lift and
counterexample route indices.
-/
theorem
    cap5FreePeeledCollarMappedCutObstructionRealizedCandidateFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarMappedCutObstructionRealizedCandidateFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRealizedCandidateLiftFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRealizedCandidateCounterexampleFoundationRouteIndexTarget := by
  have hmapped :
      CAP5FreePeeledCollarMappedCutFoundationTargetIndex :=
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_obstructionRealizedCandidateFoundationTargetIndex
      hindex
  have hmappedRoutes :=
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_routeIndexTargets
      hmapped
  have hcandidateRoutes :=
    cap5FreeRealizedCandidateLiftFoundationTarget_routeIndexTargets
      hindex.2.2.2
  exact
    ⟨hmappedRoutes.1,
      hmappedRoutes.2.1,
      hmappedRoutes.2.2,
      hcandidateRoutes.1,
      hcandidateRoutes.2⟩

/--
Closed-walk S4 salvage target for the obstruction-to-realized-candidate
foundation route.  This is the downstream statement with cyclic
five-edge-connectivity supplied by the regime route, not assumed.
-/
def Section92Step4ClosedWalkCAP5FreeMappedCutObstructionRealizedCandidateRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/--
The obstruction-to-realized-candidate target and realized-candidate lift
foundation supply the closed-walk regime-discharged S4 salvage statement.
-/
theorem
    section92Step4ClosedWalkCAP5FreeMappedCutObstructionRealizedCandidateRegimeDischargedS4SalvageTarget
    (hobstructionCandidate :
      CAP5FreeClosedWalkPeeledCollarMappedCutFaceRouteObstructionRealizedCandidateFoundationTarget)
    (hlift :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeMappedCutObstructionRealizedCandidateRegimeDischargedS4SalvageTarget := by
  intro V _ G emb source regime
  have hroute :
      Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget :=
    section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget_of_obstructionRealizedCandidateFoundationTargets
      hobstructionCandidate hlift
  exact (hroute source regime).2.2.2.2.2.2.2

/--
The public obstruction-to-realized-candidate index supplies the same explicit
closed-walk S4 salvage target.
-/
theorem
    cap5FreePeeledCollarMappedCutObstructionRealizedCandidateFoundationTargetIndex_regimeDischargedS4SalvageTarget
    (hindex :
      CAP5FreePeeledCollarMappedCutObstructionRealizedCandidateFoundationTargetIndex) :
    Section92Step4ClosedWalkCAP5FreeMappedCutObstructionRealizedCandidateRegimeDischargedS4SalvageTarget :=
  section92Step4ClosedWalkCAP5FreeMappedCutObstructionRealizedCandidateRegimeDischargedS4SalvageTarget
    hindex.2.2.1 hindex.2.2.2

end Mettapedia.GraphTheory.FourColor
