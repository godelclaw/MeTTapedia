import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeMappedCutObstruction
import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeCandidateCounterexample

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Realized-candidate interface for mapped-cut face-route obstructions.

Every mapped-cut face-route obstruction already contains the bundled small
cyclic cut whose promoted finite separator candidate realizes in the induced
peeled collar.  This module exposes that direct candidate bridge and proves
the reusable composition: the realized-candidate lift alone is the remaining
graph-facing foundation needed to rule out mapped-cut face-route obstructions
and feed the existing mapped-cut route index.
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
Every mapped-cut face-route obstruction already carries the bundled small
cyclic cut whose promoted finite separator candidate realizes.
-/
theorem offCarrierAttachmentMappedCutAvoidingFaceRouteObstructionRealizedCandidateTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    source.OffCarrierAttachmentMappedCutAvoidingFaceRouteObstructionRealizedCandidateTarget := by
  intro hobs
  rcases hobs with ⟨cut, _hcutObs⟩
  exact ⟨cut.toCyclicSeparatorCandidate, cut.toCyclicSeparatorCandidate_realizes⟩

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

/--
Under the CAP5-free regime, a mapped-cut obstruction is impossible once every
small cyclic cut in the peeled collar lifts to an ambient small cyclic cut.
-/
theorem noMappedCutFaceRouteObstruction_of_smallCutLift
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (hlift :
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph) :
    ¬ source.OffCarrierAttachmentMappedCutAvoidingFaceRouteObstruction := by
  intro hobs
  rcases hobs with ⟨cut, _hcutObs⟩
  rcases hlift cut with ⟨ambientCut, hcard⟩
  exact regime.ambient.noSmallCyclicEdgeCuts
    ⟨ambientCut, le_trans hcard cut.hcard_le_four⟩

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
The obstruction-to-realized-candidate foundation target is discharged directly
from the bundled small cyclic cut carried by each mapped-cut obstruction.
-/
theorem
    cap5FreeClosedWalkPeeledCollarMappedCutFaceRouteObstructionRealizedCandidateFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarMappedCutFaceRouteObstructionRealizedCandidateFoundationTarget := by
  intro V _ G emb source _regime
  exact
    source.offCarrierAttachmentMappedCutAvoidingFaceRouteObstructionRealizedCandidateTarget

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
Since obstruction-to-candidate is direct, the realized-candidate lift foundation
alone supplies the no-obstruction foundation.
-/
theorem
    cap5FreeClosedWalkNoMappedCutFaceRouteObstructionFoundationTarget_of_realizedCandidateLift
    (hlift :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarNoMappedCutFaceRouteObstructionFoundationTarget :=
  cap5FreeClosedWalkNoMappedCutFaceRouteObstructionFoundationTarget_of_obstructionRealizedCandidateFoundationTarget_of_realizedCandidateLift
    cap5FreeClosedWalkPeeledCollarMappedCutFaceRouteObstructionRealizedCandidateFoundationTarget
    hlift

/--
The graph-facing small-cut lift foundation directly rules out mapped-cut
face-route obstructions.
-/
theorem
    cap5FreeClosedWalkNoMappedCutFaceRouteObstructionFoundationTarget_of_smallCutLift
    (hlift :
      CAP5FreePeeledCollarSmallCutLiftFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarNoMappedCutFaceRouteObstructionFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.noMappedCutFaceRouteObstruction_of_smallCutLift
      regime (hlift regime)

/--
The selected-source small-cut lift foundation directly rules out mapped-cut
face-route obstructions.
-/
theorem
    cap5FreeClosedWalkNoMappedCutFaceRouteObstructionFoundationTarget_of_closedWalkSmallCutLift
    (hlift :
      CAP5FreeClosedWalkPeeledCollarSmallCutLiftFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarNoMappedCutFaceRouteObstructionFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.noMappedCutFaceRouteObstruction_of_smallCutLift
      regime (hlift source regime)

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
The realized-candidate lift foundation alone supplies the mapped-cut avoiding
face-route foundation.
-/
theorem
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_realizedCandidateLift
    (hlift :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget :=
  cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_obstructionRealizedCandidateFoundationTarget_of_realizedCandidateLift
    cap5FreeClosedWalkPeeledCollarMappedCutFaceRouteObstructionRealizedCandidateFoundationTarget
    hlift

/--
The graph-facing small-cut lift foundation alone supplies the mapped-cut
avoiding face-route foundation.
-/
theorem
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_smallCutLift
    (hlift :
      CAP5FreePeeledCollarSmallCutLiftFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget :=
  cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_noMappedCutFaceRouteObstructionFoundationTarget
    (cap5FreeClosedWalkNoMappedCutFaceRouteObstructionFoundationTarget_of_smallCutLift
      hlift)

/--
The selected-source small-cut lift foundation alone supplies the mapped-cut
avoiding face-route foundation.
-/
theorem
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_closedWalkSmallCutLift
    (hlift :
      CAP5FreeClosedWalkPeeledCollarSmallCutLiftFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget :=
  cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_noMappedCutFaceRouteObstructionFoundationTarget
    (cap5FreeClosedWalkNoMappedCutFaceRouteObstructionFoundationTarget_of_closedWalkSmallCutLift
      hlift)

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
Public foundation index after discharging obstruction-to-candidate: the only
closed-walk graph-facing input remaining here is realized-candidate lifting.
-/
def CAP5FreePeeledCollarMappedCutRealizedCandidateLiftFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget

/--
Reduced public foundation index for the mapped-cut route.  The first two
fields are the existing annulus separation targets; the last field is the
single graph-facing small-cut lift target.
-/
def CAP5FreePeeledCollarMappedCutSmallCutLiftFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreePeeledCollarSmallCutLiftFoundationTarget

/--
Selected-source small-cut lift public foundation index for the mapped-cut
route.  The first two fields are the existing annulus separation targets; the
last field is the closed-walk source small-cut lift target.
-/
def CAP5FreePeeledCollarMappedCutClosedWalkSmallCutLiftFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarSmallCutLiftFoundationTarget

/--
The reduced realized-candidate lift index supplies the earlier
obstruction-to-realized-candidate index.
-/
theorem
    cap5FreePeeledCollarMappedCutObstructionRealizedCandidateFoundationTargetIndex_of_realizedCandidateLiftFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarMappedCutRealizedCandidateLiftFoundationTargetIndex) :
    CAP5FreePeeledCollarMappedCutObstructionRealizedCandidateFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkPeeledCollarMappedCutFaceRouteObstructionRealizedCandidateFoundationTarget,
    hindex.2.2⟩

/--
The reduced realized-candidate lift index supplies the mapped-cut foundation
index consumed by downstream route interfaces.
-/
theorem
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_realizedCandidateLiftFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarMappedCutRealizedCandidateLiftFoundationTargetIndex) :
    CAP5FreePeeledCollarMappedCutFoundationTargetIndex :=
  cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_obstructionRealizedCandidateFoundationTargetIndex
    (cap5FreePeeledCollarMappedCutObstructionRealizedCandidateFoundationTargetIndex_of_realizedCandidateLiftFoundationTargetIndex
      hindex)

/--
The reduced small-cut lift index supplies the realized-candidate lift index.
-/
theorem
    cap5FreePeeledCollarMappedCutRealizedCandidateLiftFoundationTargetIndex_of_smallCutLiftFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarMappedCutSmallCutLiftFoundationTargetIndex) :
    CAP5FreePeeledCollarMappedCutRealizedCandidateLiftFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreePeeledCollarRealizedCandidateLiftFoundationTarget_of_smallCutLift
      hindex.2.2⟩

/--
The reduced small-cut lift index supplies the mapped-cut foundation index
consumed by downstream route interfaces.
-/
theorem
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_smallCutLiftFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarMappedCutSmallCutLiftFoundationTargetIndex) :
    CAP5FreePeeledCollarMappedCutFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_smallCutLift
      hindex.2.2⟩

/--
The selected-source small-cut lift index supplies the mapped-cut foundation
index consumed by downstream route interfaces.
-/
theorem
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_closedWalkSmallCutLiftFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarMappedCutClosedWalkSmallCutLiftFoundationTargetIndex) :
    CAP5FreePeeledCollarMappedCutFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_closedWalkSmallCutLift
      hindex.2.2⟩

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
Closed-walk route-index theorem after discharging obstruction-to-candidate.
-/
theorem
    section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget_of_realizedCandidateLift
    (hlift :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget :=
  section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget_of_obstructionRealizedCandidateFoundationTargets
    cap5FreeClosedWalkPeeledCollarMappedCutFaceRouteObstructionRealizedCandidateFoundationTarget
    hlift

/--
Closed-walk route-index theorem from the graph-facing small-cut lift
foundation.
-/
theorem
    section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget_of_smallCutLift
    (hlift :
      CAP5FreePeeledCollarSmallCutLiftFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget :=
  section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget
    (cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_smallCutLift
      hlift)

/--
Closed-walk route-index theorem from the selected-source small-cut lift
foundation.
-/
theorem
    section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget_of_closedWalkSmallCutLift
    (hlift :
      CAP5FreeClosedWalkPeeledCollarSmallCutLiftFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget :=
  section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget
    (cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_closedWalkSmallCutLift
      hlift)

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
The reduced realized-candidate lift index supplies the mapped-cut route
indices, plus the graph-facing realized-candidate lift and counterexample
route indices.
-/
theorem
    cap5FreePeeledCollarMappedCutRealizedCandidateLiftFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarMappedCutRealizedCandidateLiftFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRealizedCandidateLiftFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRealizedCandidateCounterexampleFoundationRouteIndexTarget :=
  cap5FreePeeledCollarMappedCutObstructionRealizedCandidateFoundationTargetIndex_routeIndexTargets
    (cap5FreePeeledCollarMappedCutObstructionRealizedCandidateFoundationTargetIndex_of_realizedCandidateLiftFoundationTargetIndex
      hindex)

/--
The reduced small-cut lift index supplies the mapped-cut route indices, plus
the graph-facing realized-candidate lift and counterexample route indices.
-/
theorem
    cap5FreePeeledCollarMappedCutSmallCutLiftFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarMappedCutSmallCutLiftFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRealizedCandidateLiftFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRealizedCandidateCounterexampleFoundationRouteIndexTarget :=
  cap5FreePeeledCollarMappedCutRealizedCandidateLiftFoundationTargetIndex_routeIndexTargets
    (cap5FreePeeledCollarMappedCutRealizedCandidateLiftFoundationTargetIndex_of_smallCutLiftFoundationTargetIndex
      hindex)

/--
The selected-source small-cut lift index supplies the mapped-cut route indices
and the closed-walk small-cut lift route index.
-/
theorem
    cap5FreePeeledCollarMappedCutClosedWalkSmallCutLiftFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarMappedCutClosedWalkSmallCutLiftFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeSmallCutLiftFoundationRouteIndexTarget :=
  ⟨section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget
      hindex.1,
    section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget
      hindex.2.1,
    section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget_of_closedWalkSmallCutLift
      hindex.2.2,
    section92Step4ClosedWalkCAP5FreeSmallCutLiftFoundationRouteIndexTarget
      hindex.2.2⟩

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
Closed-walk S4 salvage target for the small-cut lift foundation route.  This
is the same downstream statement with cyclic five-edge-connectivity supplied
by the CAP5-free regime route, not assumed.
-/
def Section92Step4ClosedWalkCAP5FreeMappedCutSmallCutLiftRegimeDischargedS4SalvageTarget :
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

/--
The reduced realized-candidate lift index supplies the explicit closed-walk S4
salvage target.
-/
theorem
    cap5FreePeeledCollarMappedCutRealizedCandidateLiftFoundationTargetIndex_regimeDischargedS4SalvageTarget
    (hindex :
      CAP5FreePeeledCollarMappedCutRealizedCandidateLiftFoundationTargetIndex) :
    Section92Step4ClosedWalkCAP5FreeMappedCutObstructionRealizedCandidateRegimeDischargedS4SalvageTarget :=
  cap5FreePeeledCollarMappedCutObstructionRealizedCandidateFoundationTargetIndex_regimeDischargedS4SalvageTarget
    (cap5FreePeeledCollarMappedCutObstructionRealizedCandidateFoundationTargetIndex_of_realizedCandidateLiftFoundationTargetIndex
      hindex)

/--
The small-cut lift foundation supplies the closed-walk regime-discharged S4
salvage statement directly.
-/
theorem
    section92Step4ClosedWalkCAP5FreeMappedCutSmallCutLiftRegimeDischargedS4SalvageTarget
    (hlift :
      CAP5FreePeeledCollarSmallCutLiftFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeMappedCutSmallCutLiftRegimeDischargedS4SalvageTarget := by
  intro V _ G emb source regime
  exact
    (MinimalCounterexamplePeeledCollarRegime.routeIndexConsequences_of_cap5FreeSmallCutLiftFoundationTarget
      hlift regime).2.2.2

/--
The reduced small-cut lift index supplies the explicit closed-walk S4 salvage
target.
-/
theorem
    cap5FreePeeledCollarMappedCutSmallCutLiftFoundationTargetIndex_regimeDischargedS4SalvageTarget
    (hindex :
      CAP5FreePeeledCollarMappedCutSmallCutLiftFoundationTargetIndex) :
    Section92Step4ClosedWalkCAP5FreeMappedCutSmallCutLiftRegimeDischargedS4SalvageTarget :=
  section92Step4ClosedWalkCAP5FreeMappedCutSmallCutLiftRegimeDischargedS4SalvageTarget
    hindex.2.2

/--
The selected-source small-cut lift foundation supplies the closed-walk
regime-discharged S4 salvage statement directly.
-/
theorem
    section92Step4ClosedWalkCAP5FreeMappedCutSmallCutLiftRegimeDischargedS4SalvageTarget_of_closedWalkSmallCutLift
    (hlift :
      CAP5FreeClosedWalkPeeledCollarSmallCutLiftFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeMappedCutSmallCutLiftRegimeDischargedS4SalvageTarget := by
  intro V _ G emb source regime
  exact
    (source.routeIndexConsequences_of_cap5FreeSmallCutLiftFoundationTarget
      hlift regime).2.2.2

/--
The selected-source small-cut lift index supplies the explicit closed-walk S4
salvage target.
-/
theorem
    cap5FreePeeledCollarMappedCutClosedWalkSmallCutLiftFoundationTargetIndex_regimeDischargedS4SalvageTarget
    (hindex :
      CAP5FreePeeledCollarMappedCutClosedWalkSmallCutLiftFoundationTargetIndex) :
    Section92Step4ClosedWalkCAP5FreeMappedCutSmallCutLiftRegimeDischargedS4SalvageTarget :=
  section92Step4ClosedWalkCAP5FreeMappedCutSmallCutLiftRegimeDischargedS4SalvageTarget_of_closedWalkSmallCutLift
    hindex.2.2

end Mettapedia.GraphTheory.FourColor
